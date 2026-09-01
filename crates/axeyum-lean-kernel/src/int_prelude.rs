//! The **integer prelude** (ADR-0042, the integer-arithmetic / Diophantine
//! reconstruction foundation): `ℤ` **constructed** over the proved `ℕ`
//! development, declared into a [`Kernel`]'s environment through the trusted
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration) and
//! [`Kernel::add_inductive`](crate::Kernel::add_inductive) gates.
//!
//! This is the trusted base for reconstructing **integer-cut / Diophantine
//! `QF_LIA`** refutations into kernel-checked Lean terms. An integer-infeasibility
//! proof is, at bottom, a chain of order/ring steps over `ℤ` that — unlike the
//! ordered field `R` — can invoke **discreteness** (`no_int_between`: there is no
//! integer strictly between `0` and `1`) to refute a residue `g·m = r` with
//! `0 < r < g`.
//!
//! ## Constructed, not asserted
//!
//! `Int` is a real inductive over `Nat` — `Int.ofNat n` for `n ≥ 0`,
//! `Int.negSucc n` for `-(n+1)` — and every operation is a checked definition
//! by structural recursion (see [`defs`]). The laws are then **theorems** the
//! kernel type-checks at admission, proved from the axiom-free `Nat` prelude;
//! what remains asserted is listed in [`build_int_prelude`] and is exactly the
//! part this development has not yet derived.
//!
//! The normalized-constructor representation is deliberate. A setoid quotient
//! of `ℕ × ℕ` is the other textbook route, and in *this* kernel it is not
//! available at all: [`Kernel::add_quotient_package`](crate::Kernel) admits
//! exactly four declarations — `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` — and
//! **there is no `Quot.sound`**, so nothing can prove two `Quot.mk`s equal and
//! a quotient carrier has a quotient's shape with none of its content. (This
//! paragraph used to say the route was merely *expensive*, because
//! `Quot.sound` would enter every footprint; that describes Lean's package, not
//! ours. Measured and pinned in ADR-0456.) With `ofNat`/`negSucc` each integer
//! has exactly one representative, `Eq Int` is ordinary propositional equality,
//! and a derived law's footprint is genuinely empty.
//!
//! ## What is declared
//!
//! The carrier lives in `Type = Sort 1`; the relations land in `Prop = Sort 0`:
//!
//! - **Carrier** `Int : Type`, an inductive with constructors
//!   `Int.ofNat : Nat → Int` and `Int.negSucc : Nat → Int` and a
//!   kernel-generated recursor `Int.rec`.
//! - **Normalizers** `Int.negOfNat : Nat → Int` and
//!   `Int.subNatNat : Nat → Nat → Int` (definitions).
//! - **Operations** (definitions): `add`, `mul`, `neg`, `zero`, `one`.
//! - **Relations** (definitions): `le`, `lt`, each by cases into `Nat.le` /
//!   `Nat.lt`.
//! - **The `subNatNat` borrow development** (see [`sub_nat_nat`]): the shift
//!   lemma, the two characterisations, and the elimination principle that says
//!   which constructor a normalized difference lands in. Everything that mixes
//!   `Int.add` with a second operation or relation goes through it.
//! - **Laws**: the order, additive, multiplicative and discreteness facts named
//!   on the [`IntPrelude`] fields below — theorems where derived, axioms
//!   otherwise.
//!
//! The propositional connectives (`Not`, `And`, `Or`, `Eq`, `Exists`, `False`)
//! come from [`build_logic_prelude`](crate::build_logic_prelude); `Eq` is used
//! at universe `u := 1` because the carrier is `Sort 1`.
// Proof scripts are long, straight-line term constructions with short
// mathematical names; splitting them would obscure the derivation they mirror.
// `type_complexity` / `too_many_arguments`: the declaration and case-analysis
// helpers take `&dyn Fn(&mut IntDev<'_>, …) -> …` builders, which no type alias
// can shorten without hiding the signature — the same trade-off `nat_prelude`
// documents.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::type_complexity,
    clippy::large_types_passed_by_value
)]

use crate::name::NameId;
use crate::nat_prelude::{NatPrelude, build_nat_prelude};
use crate::{Kernel, KernelError, LogicPrelude, PreludeKey, PreludeValue};

mod add_basics;
mod algebra;
mod bezout_witnesses;
mod crt;
mod decide;
mod defs;
mod division;
mod dvd;
mod dvd_gcd_mirrors;
mod dvd_mul_split;
mod euclid;
mod euler;
mod euler_assembly;
mod euler_prod_coprime;
mod euler_prod_factor;
mod euler_prod_modeq;
mod euler_prod_pow;
mod euler_theorem;
mod euler_totient;
mod euler_unit_preserve;
mod euler_unit_range;
mod exists_gcd_one;
mod fibonacci;
mod first_supplementary;
mod first_supplementary_residue;
mod gauss_assembly;
mod gauss_factorial_coprime;
mod gauss_factorial_product;
mod gauss_sign_product;
mod gauss_term_congruence;
mod gcd;
mod gcd_dvd_iff;
mod gcd_scaled_mirrors;
mod modeq;
mod modeq_cancel_div_gcd;
mod modeq_family;
mod modinv;
mod nat_abs;
pub(crate) mod ops;
mod order;
mod order_add;
mod order_coercion;
mod parity;
mod prime_dvd_mul_mirrors;
mod prod;
mod qr_criterion;
mod rat;
mod ring;
mod second_supplementary;
mod sign;
mod sign_product;
mod statements;
mod sub;
mod sub_nat_nat;
mod sum;
mod sum_maps;
mod two_sided_induction;
mod wilson;

use ops::IntDev;

/// The interned names produced by [`build_int_prelude`]: the carrier, its
/// constructors and recursor, the ring/order operations, and every law of the
/// discretely-ordered commutative ring, plus the embedded [`NatPrelude`] the
/// construction rests on.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels. All fields are public so tests and callers can build `Const` terms
/// (`k.const_(int.le, vec![])`, `k.const_(int.no_int_between, vec![])`, …).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntPrelude {
    /// The embedded logical prelude (`False`, `Not`, `And`, `Eq`, …).
    pub logic: LogicPrelude,
    /// The natural-number development `Int` is constructed over. Its own axiom
    /// footprint is empty, which is what makes a derived integer law's
    /// footprint empty too.
    pub nat: NatPrelude,

    // --- carrier + constructors ---------------------------------------------
    /// `Int : Type` (i.e. `Int : Sort 1`) — the inductive carrier.
    pub z: NameId,
    /// `Int.ofNat : Nat → Int` — the non-negative constructor.
    pub of_nat: NameId,
    /// `Int.negSucc : Nat → Int` — the constructor for `-(n+1)`.
    pub neg_succ: NameId,
    /// `Int.rec` — the kernel-generated recursor.
    pub rec: NameId,
    /// `Int.negOfNat : Nat → Int` — the integer `-n` for a natural `n`.
    pub neg_of_nat: NameId,
    /// `Int.subNatNat : Nat → Nat → Int` — the normalized difference `m - n`.
    pub sub_nat_nat: NameId,

    // --- the `subNatNat` borrow development ----------------------------------
    /// `subNatNat_succ_succ : ∀ (m n : Nat), subNatNat (succ m) (succ n) = subNatNat m n`.
    pub sub_nat_nat_succ_succ: NameId,
    /// `subNatNat_add_add : ∀ (m n k : Nat), subNatNat (m+k) (n+k) = subNatNat m n`.
    pub sub_nat_nat_add_add: NameId,
    /// `subNatNat_add_add_left : ∀ (k m n : Nat), subNatNat (k+m) (k+n) = subNatNat m n`.
    pub sub_nat_nat_add_add_left: NameId,
    /// `subNatNat_zero : ∀ (m : Nat), subNatNat m 0 = ofNat m`.
    pub sub_nat_nat_zero: NameId,
    /// `zero_subNatNat : ∀ (k : Nat), subNatNat 0 k = negOfNat k`.
    pub zero_sub_nat_nat: NameId,
    /// `subNatNat_add_left : ∀ (n i : Nat), subNatNat (n+i) n = ofNat i` — the
    /// borrow **does not** fire when the first argument dominates.
    pub sub_nat_nat_add_left: NameId,
    /// `subNatNat_add_right : ∀ (m k : Nat), subNatNat m (m+k) = negOfNat k` —
    /// the borrow fires, and the answer is the negation of the excess.
    pub sub_nat_nat_add_right: NameId,
    /// `subNatNat_elim : ∀ (P : Int → Prop) (m n : Nat),
    /// (∀ i, n+i = m → P (ofNat i)) → (∀ i, m+(i+1) = n → P (negSucc i)) →
    /// P (subNatNat m n)` — the case analysis the borrow's two outcomes support.
    pub sub_nat_nat_elim: NameId,

    // --- `Int.add` against `subNatNat` and `negOfNat` -------------------------
    /// `ofNat_add_subNatNat : ∀ m n q, ofNat m + subNatNat n q = subNatNat (m+n) q`.
    pub of_nat_add_sub_nat_nat: NameId,
    /// `subNatNat_add_ofNat : ∀ a b p, subNatNat a b + ofNat p = subNatNat (a+p) b`.
    pub sub_nat_nat_add_of_nat: NameId,
    /// `subNatNat_add_negSucc : ∀ a b p, subNatNat a b + negSucc p = subNatNat a (b+(p+1))`.
    pub sub_nat_nat_add_neg_succ: NameId,
    /// `negSucc_add_subNatNat : ∀ m a b, negSucc m + subNatNat a b = subNatNat a (b+(m+1))`.
    pub neg_succ_add_sub_nat_nat: NameId,
    /// `ofNat_add_negOfNat : ∀ u v, ofNat u + negOfNat v = subNatNat u v`.
    pub of_nat_add_neg_of_nat: NameId,
    /// `negOfNat_add_ofNat : ∀ v u, negOfNat v + ofNat u = subNatNat u v`.
    pub neg_of_nat_add_of_nat: NameId,
    /// `negOfNat_add_negOfNat : ∀ u v, negOfNat u + negOfNat v = negOfNat (u+v)`.
    pub neg_of_nat_add_neg_of_nat: NameId,
    /// `negOfNat_add_subNatNat : ∀ mag base offset,
    /// negOfNat mag + subNatNat base offset = subNatNat base (offset+mag)`.
    pub neg_of_nat_add_sub_nat_nat: NameId,

    // --- `Int.mul` against `negOfNat` and `subNatNat` -------------------------
    /// `mul_ofNat_negOfNat : ∀ m k, ofNat m * negOfNat k = negOfNat (m*k)`.
    pub mul_of_nat_neg_of_nat: NameId,
    /// `mul_negOfNat_ofNat : ∀ k n, negOfNat k * ofNat n = negOfNat (k*n)`.
    pub mul_neg_of_nat_of_nat: NameId,
    /// `mul_negSucc_negOfNat : ∀ m k, negSucc m * negOfNat k = ofNat ((m+1)*k)`.
    pub mul_neg_succ_neg_of_nat: NameId,
    /// `mul_negOfNat_negSucc : ∀ k n, negOfNat k * negSucc n = ofNat (k*(n+1))`.
    pub mul_neg_of_nat_neg_succ: NameId,
    /// `ofNat_mul_subNatNat : ∀ m p q, ofNat m * subNatNat p q = subNatNat (m*p) (m*q)`.
    pub of_nat_mul_sub_nat_nat: NameId,
    /// `negSucc_mul_subNatNat :
    /// ∀ m p q, negSucc m * subNatNat p q = subNatNat ((m+1)*q) ((m+1)*p)`.
    pub neg_succ_mul_sub_nat_nat: NameId,

    // --- the order, as a difference ------------------------------------------
    /// `le_ofNat_add : ∀ (a : Int) (i : Nat), le a (a + ofNat i)`.
    pub le_of_nat_add: NameId,
    /// `le_dest : ∀ (a b : Int), le a b → ∃ (i : Nat), b = a + ofNat i`.
    pub le_dest: NameId,
    /// `lt_ofNat_add : ∀ (a : Int) (i : Nat), lt a (a + ofNat (i+1))`.
    pub lt_of_nat_add: NameId,
    /// `lt_dest : ∀ (a b : Int), lt a b → ∃ (i : Nat), b = a + ofNat (i+1)`.
    pub lt_dest: NameId,
    /// `le_of_ofNat_le_ofNat : ∀ {m n : Nat}, le (ofNat m) (ofNat n) → Nat.le m n`
    /// — Mathlib's coercion-order lemma. `Int.le (ofNat m) (ofNat n)` is
    /// definitionally `Nat.le m n` (`define_binary_int`'s `of_of` branch for
    /// `p.le` is literally `NatOps::le`), so the proof is the hypothesis
    /// itself under that defeq.
    pub le_of_ofnat_le_ofnat: NameId,
    /// `lt_of_ofNat_lt_ofNat : ∀ {n m : Nat}, lt (ofNat n) (ofNat m) → Nat.lt n m`
    /// — the `lt` sibling of [`le_of_ofnat_le_ofnat`](Self::le_of_ofnat_le_ofnat),
    /// same defeq argument against `NatOps::lt`.
    pub lt_of_ofnat_lt_ofnat: NameId,
    /// `Int.le.elim : ∀ {a b}, le a b → ∀ {P : Prop}, (∀ (n : Nat), a + ofNat n = b → P) → P`
    /// — the CPS elimination form of [`le_dest`](Self::le_dest)'s existential,
    /// built by `Exists.elim` (`ops::exists_elim`) over `le_dest`'s witness,
    /// flipping its `b = a + ofNat i` equation with `isymm`. Declared as a
    /// child of `le` (`Int.le.elim`), not of `Int` directly — the same
    /// namespacing `Nat.le.step` uses for a name under an unrelated head.
    pub le_elim: NameId,
    /// `Int.lt.elim : ∀ {a b}, lt a b → ∀ {P : Prop}, (∀ (n : Nat), a + ofNat n.succ = b → P) → P`
    /// — the `lt` sibling of [`le_elim`](Self::le_elim), built the same way
    /// from [`lt_dest`](Self::lt_dest).
    pub lt_elim: NameId,

    // --- operations ----------------------------------------------------------
    /// `add : Int → Int → Int`.
    pub add: NameId,
    /// `mul : Int → Int → Int`.
    pub mul: NameId,
    /// `neg : Int → Int`.
    pub neg: NameId,
    /// `sub : Int → Int → Int := fun a b => add a (neg b)` — a plain
    /// `Definition`, not a fresh inductive operation: every law about it
    /// (`mul_sub`, `modEq_iff_dvd`'s difference) is proved by unfolding to
    /// `add`/`neg` and folding back, the same defeq-bridging idiom
    /// `Int.dvd`/`Int.ModEq` already use.
    pub sub: NameId,
    /// `zero : Int`.
    pub zero: NameId,
    /// `one : Int`.
    pub one: NameId,
    /// `le : Int → Int → Prop`.
    pub le: NameId,
    /// `lt : Int → Int → Prop`.
    pub lt: NameId,

    // --- order laws ----------------------------------------------------------
    /// `le_refl : ∀ (a : Int), le a a`.
    pub le_refl: NameId,
    /// `le_trans : ∀ (a b c : Int), le a b → le b c → le a c`.
    pub le_trans: NameId,
    /// `lt_irrefl : ∀ (a : Int), Not (lt a a)`.
    pub lt_irrefl: NameId,
    /// `lt_trans : ∀ (a b c : Int), lt a b → lt b c → lt a c`.
    pub lt_trans: NameId,
    /// `lt_of_lt_of_le : ∀ (a b c : Int), lt a b → le b c → lt a c`.
    pub lt_of_lt_of_le: NameId,
    /// `lt_of_le_of_lt : ∀ (a b c : Int), le a b → lt b c → lt a c`.
    pub lt_of_le_of_lt: NameId,
    /// `le_of_lt : ∀ (a b : Int), lt a b → le a b`.
    pub le_of_lt: NameId,

    // --- additive laws -------------------------------------------------------
    /// `add_le_add : ∀ (a b c d : Int), le a b → le c d → le (add a c) (add b d)`.
    pub add_le_add: NameId,
    /// `add_comm : ∀ (a b : Int), Eq Int (add a b) (add b a)`.
    pub add_comm: NameId,
    /// `add_assoc : ∀ (a b c : Int), Eq Int (add (add a b) c) (add a (add b c))`.
    pub add_assoc: NameId,
    /// `add_zero : ∀ (a : Int), Eq Int (add a zero) a`.
    pub add_zero: NameId,
    /// `add_neg : ∀ (a : Int), Eq Int (add a (neg a)) zero`.
    pub add_neg: NameId,
    /// `add_neg_cancel_right : ∀ (a b : Int),
    /// Eq Int (add (add a b) (neg b)) a`.
    pub add_neg_cancel_right: NameId,
    /// `add_left_neg : ∀ (a : Int), Eq Int (add (neg a) a) zero`.
    pub add_left_neg: NameId,
    /// `add_neg_eq_sub : ∀ (a b : Int), Eq Int (add a (neg b)) (sub a b)`.
    pub add_neg_eq_sub: NameId,
    /// `add_left_comm : ∀ (a b c : Int),
    /// Eq Int (add a (add b c)) (add b (add a c))`.
    pub add_left_comm: NameId,
    /// `add_mul : ∀ (a b c : Int),
    /// Eq Int (mul (add a b) c) (add (mul a c) (mul b c))`.
    pub add_mul: NameId,
    /// `add_neg_cancel_left : ∀ (a b : Int),
    /// Eq Int (add a (add (neg a) b)) b`.
    pub add_neg_cancel_left: NameId,
    /// `add_left_cancel : ∀ (a b c : Int),
    /// Eq Int (add a b) (add a c) → Eq Int b c`.
    pub add_left_cancel: NameId,
    /// `add_left_inj : ∀ (i j k : Int),
    /// Iff (Eq Int (add i k) (add j k)) (Eq Int i j)`.
    pub add_left_inj: NameId,
    /// `add_lt_add_of_le_of_lt :
    /// ∀ (a b c d : Int), le a b → lt c d → lt (add a c) (add b d)`.
    pub add_lt_add_of_le_of_lt: NameId,
    /// `add_le_add_left : ∀ (a b : Int), le a b → ∀ (c : Int), le (add c a) (add c b)`.
    pub add_le_add_left: NameId,
    /// `add_le_add_right : ∀ (a b : Int), le a b → ∀ (c : Int), le (add a c) (add b c)`.
    pub add_le_add_right: NameId,
    /// `add_le_add_iff_left : ∀ (b c a : Int), Iff (le (add a b) (add a c)) (le b c)`.
    pub add_le_add_iff_left: NameId,
    /// `add_le_add_iff_right : ∀ (a b c : Int), Iff (le (add a c) (add b c)) (le a b)`.
    pub add_le_add_iff_right: NameId,
    /// `add_le_add_three :
    /// ∀ (a b c d e f : Int), le a d → le b e → le c f →
    /// le (add (add a b) c) (add (add d e) f)`.
    pub add_le_add_three: NameId,
    /// `add_le_iff_le_sub : ∀ (a b c : Int), Iff (le (add a b) c) (le a (sub c b))`.
    pub add_le_iff_le_sub: NameId,
    /// `add_le_of_le_neg_add : ∀ (a b c : Int), le b (add (neg a) c) → le (add a b) c`.
    pub add_le_of_le_neg_add: NameId,
    /// `add_le_of_le_sub_left : ∀ (a b c : Int), le b (sub c a) → le (add a b) c`.
    pub add_le_of_le_sub_left: NameId,
    /// `add_le_of_le_sub_right : ∀ (a b c : Int), le a (sub c b) → le (add a b) c`.
    pub add_le_of_le_sub_right: NameId,

    // --- multiplicative / ring laws -----------------------------------------
    /// `mul_le_mul_of_nonneg_left :
    /// ∀ (a b c : Int), le zero a → le b c → le (mul a b) (mul a c)`.
    pub mul_le_mul_of_nonneg_left: NameId,
    /// `zero_lt_one : lt zero one`.
    pub zero_lt_one: NameId,
    /// `mul_comm : ∀ (a b : Int), Eq Int (mul a b) (mul b a)`.
    pub mul_comm: NameId,
    /// `mul_assoc : ∀ (a b c : Int), Eq Int (mul (mul a b) c) (mul a (mul b c))`.
    pub mul_assoc: NameId,
    /// `mul_one : ∀ (a : Int), Eq Int (mul a one) a`.
    pub mul_one: NameId,
    /// `one_mul : ∀ (a : Int), Eq Int (mul one a) a`.
    pub one_mul: NameId,
    /// `neg_one_mul : ∀ (a : Int), Eq Int (mul (neg one) a) (neg a)`.
    pub neg_one_mul: NameId,
    /// `mul_zero : ∀ (a : Int), Eq Int (mul a zero) zero`.
    pub mul_zero: NameId,
    /// `left_distrib :
    /// ∀ (a b c : Int), Eq Int (mul a (add b c)) (add (mul a b) (mul a c))`.
    pub left_distrib: NameId,
    /// `mul_neg : ∀ (a b : Int), Eq Int (mul a (neg b)) (neg (mul a b))` —
    /// derived from `mul_comm`/`mul_assoc`/`neg_one_mul` alone, no case split.
    pub mul_neg: NameId,
    /// `mul_sub :
    /// ∀ (a x y : Int), Eq Int (mul a (sub x y)) (sub (mul a x) (mul a y))` —
    /// `left_distrib` plus `mul_neg`, unfolding `sub` and folding it back.
    pub mul_sub: NameId,
    /// `mul_nonneg : ∀ (a b : Int), le zero a → le zero b → le zero (mul a b)`.
    pub mul_nonneg: NameId,
    /// `mul_pos : ∀ (a b : Int), lt zero a → lt zero b → lt zero (mul a b)` —
    /// the strict form `mul_nonneg` lacked; `crt_unique` used to take
    /// `0 < m*n` as an explicit hypothesis for exactly this reason.
    pub mul_pos: NameId,
    /// `sq_nonneg : ∀ (a : Int), le zero (mul a a)` — *unconditional*
    /// square-nonnegativity, sign-independent (unlike [`Self::mul_nonneg`],
    /// which needs both factors nonnegative). This is the nonnegativity
    /// primitive a sum-of-squares certificate rests on.
    pub sq_nonneg: NameId,
    /// `mul_nonneg_of_nonneg_or_nonpos :
    /// ∀ (a b : Int), (le zero a ∧ le zero b) ∨ (le a zero ∧ le b zero) →
    /// le zero (mul a b)` — `Mathlib` `Int.mul_nonneg_of_nonneg_or_nonpos`,
    /// the direct implication `mul_nonneg_iff`'s backward direction is built
    /// from.
    pub mul_nonneg_of_nonneg_or_nonpos: NameId,
    /// `mul_nonneg_iff :
    /// Iff (le zero (mul a b)) ((le zero a ∧ le zero b) ∨ (le a zero ∧ le b
    /// zero))` — `Mathlib` `Int.mul_nonneg_iff`.
    pub mul_nonneg_iff: NameId,
    /// `mul_pos_iff :
    /// Iff (lt zero (mul a b)) ((lt zero a ∧ lt zero b) ∨ (lt a zero ∧ lt b
    /// zero))` — `Mathlib` `Int.mul_pos_iff`.
    pub mul_pos_iff: NameId,
    /// `mul_neg_iff :
    /// Iff (lt (mul a b) zero) ((lt zero a ∧ lt b zero) ∨ (lt a zero ∧ lt
    /// zero b))` — `Mathlib` `Int.mul_neg_iff`.
    pub mul_neg_iff: NameId,
    /// `mul_nonpos_iff :
    /// Iff (le (mul a b) zero) ((le zero a ∧ le b zero) ∨ (le a zero ∧ le
    /// zero b))` — `Mathlib` `Int.mul_nonpos_iff`.
    pub mul_nonpos_iff: NameId,

    // --- `Int.pow : Int → Nat → Int` -----------------------------------------
    /// `Int.pow : Int → Nat → Int` — structural recursion on the natural
    /// exponent, `pow a zero ≡ one` and `pow a (succ j) ≡ mul (pow a j) a`,
    /// mirroring `Nat.pow`'s own convention exactly. A checked definition, not
    /// an axiom.
    pub pow: NameId,
    /// `pow_zero : ∀ (a : Int), Eq Int (pow a zero) one` — closes by `Eq.refl`.
    pub pow_zero: NameId,
    /// `pow_succ : ∀ (a : Int) (m : Nat), Eq Int (pow a (succ m)) (mul (pow a m) a)`
    /// — closes by `Eq.refl`. Quantifies over one `Int` and one `Nat`, so it is
    /// declared by hand rather than through `ops::IntDev::int_theorem`.
    pub pow_succ: NameId,
    /// `pow_add : ∀ (a : Int) (m n : Nat), Eq Int (pow a (add m n)) (mul (pow a m) (pow a n))`
    /// — induction on `n`, mirroring `Nat.pow_add`'s own proof shape.
    pub pow_add: NameId,
    /// `pow_mul : ∀ (a : Int) (m n : Nat),
    /// Eq Int (pow a (m*n)) (pow (pow a m) n)`.
    pub pow_mul: NameId,

    // --- `Int.prodRange : (Nat → Int) → Nat → Int` ---------------------------
    /// `Int.prodRange : (Nat → Int) → Nat → Int` — structural recursion on the
    /// `Nat` bound, `prodRange f zero ≡ one` and
    /// `prodRange f (succ n) ≡ mul (prodRange f n) (f n)`, mirroring
    /// `Nat.sumRange`'s own convention exactly (exclusive bound, new factor
    /// multiplied onto the right of the prior product). A checked definition,
    /// not an axiom.
    pub prod_range: NameId,
    /// `sumRange : (Nat → Int) → Nat → Int` — the **signed** finite sum,
    /// `sumRange f n = f 0 + … + f (n−1)`, exclusive bound, `Int.zero` at the
    /// base, fresh term added on the right. The `Int` counterpart of
    /// [`Self::prod_range`], and the aggregate Eisenstein's lemma needs because
    /// it subtracts inside a sum. `sum.rs::declare_sum_range`.
    pub sum_range: NameId,
    /// `sumRange_zero : ∀ f, Eq Int (sumRange f zero) zero` — `Eq.refl`.
    pub sum_range_zero: NameId,
    /// `sumRange_succ : ∀ f n,
    /// Eq Int (sumRange f (succ n)) (add (sumRange f n) (f n))` — `Eq.refl`.
    pub sum_range_succ: NameId,
    /// `sumRange_congr : ∀ f g n, (∀ k, Eq Int (f k) (g k)) →
    /// Eq Int (sumRange f n) (sumRange g n)`.
    pub sum_range_congr: NameId,
    /// `sumRange_add : ∀ f g n,
    /// Eq Int (sumRange (fun k => add (f k) (g k)) n)
    ///        (add (sumRange f n) (sumRange g n))`.
    pub sum_range_add: NameId,
    /// `sumRange_neg : ∀ f n,
    /// Eq Int (sumRange (fun k => neg (f k)) n) (neg (sumRange f n))`.
    pub sum_range_neg: NameId,
    /// `sumRange_sub : ∀ f g n,
    /// Eq Int (sumRange (fun k => sub (f k) (g k)) n)
    ///        (sub (sumRange f n) (sumRange g n))` — subtraction inside a
    /// finite sum, the step `Int.prodRange` has no analogue of.
    pub sum_range_sub: NameId,
    /// `sumRange_ofNat : ∀ (f : Nat → Nat) n,
    /// Eq Int (sumRange (fun k => ofNat (f k)) n) (ofNat (Nat.sumRange f n))`
    /// — the ℕ→ℤ bridge that lets a lattice-point count enter a signed
    /// identity.
    pub sum_range_of_nat: NameId,
    /// `sumRange_mul_right : ∀ f z n,
    /// Eq Int (sumRange (fun k => mul (f k) z) n) (mul (sumRange f n) z)`
    /// — pull a constant right factor out of a finite sum (`sum_maps.rs`).
    pub sum_range_mul_right: NameId,
    /// `sumRange_mul_left : ∀ z f n,
    /// Eq Int (sumRange (fun k => mul z (f k)) n) (mul z (sumRange f n))`
    /// — pull a constant left factor out of a finite sum (`sum_maps.rs`).
    pub sum_range_mul_left: NameId,
    /// `sumMaps : Nat → Nat → ((Nat → Nat) → Int) → Int` — a finite sum
    /// indexed by the **function space** `[0,m) → [0,n)`, folded by structural
    /// recursion on `m` with a higher-order motive. See `sum_maps.rs`: this is
    /// the construction that shows ADR-1135's "the index set of the outer sum
    /// is a function space, not a `Nat` range" is not an obstruction.
    pub sum_maps: NameId,
    /// `sumMaps_zero : ∀ n F, Eq Int (sumMaps 0 n F) (F (fun _ => 0))`.
    pub sum_maps_zero: NameId,
    /// `sumMaps_succ : ∀ m n F, Eq Int (sumMaps (succ m) n F)
    /// (sumRange (fun k => sumMaps m n (fun g => F (cons k g))) n)`.
    pub sum_maps_succ: NameId,
    /// `sumMaps_congr : ∀ n m F G, (∀ g, Eq Int (F g) (G g))
    /// → Eq Int (sumMaps m n F) (sumMaps m n G)`.
    pub sum_maps_congr: NameId,
    /// `sumMaps_mul_left : ∀ n z m H,
    /// Eq Int (sumMaps m n (fun g => mul z (H g))) (mul z (sumMaps m n H))`.
    pub sum_maps_mul_left: NameId,
    /// `prodRange_sumRange_expand : ∀ n m (c : Nat → Nat → Int),
    /// Eq Int (prodRange (fun i => sumRange (c i) n) m)
    /// (sumMaps m n (fun g => prodRange (fun i => c i (g i)) m))`
    /// — the **generalized distributive law**: a product of `m` sums of `n`
    /// terms expands into a sum over all `n^m` maps `[0,m) → [0,n)`. This is
    /// the Cauchy–Binet expansion step ADR-1135 recorded as inexpressible.
    pub prod_range_sum_range_expand: NameId,
    /// `neg_add : ∀ a b, Eq Int (neg (add a b)) (add (neg a) (neg b))`.
    /// The proof already existed as `modeq.rs`'s private helper; this is the
    /// first time it is stated as a theorem.
    pub neg_add: NameId,
    /// `prodRange_zero : ∀ f, Eq Int (prodRange f zero) one` — closes by
    /// `Eq.refl`.
    pub prod_range_zero: NameId,
    /// `prodRange_succ : ∀ f n, Eq Int (prodRange f (succ n)) (mul (prodRange f n) (f n))`
    /// — closes by `Eq.refl`.
    pub prod_range_succ: NameId,
    /// `prodRange_shiftFront : ∀ f n, Eq Int (prodRange f (succ n))
    ///   (mul (f zero) (prodRange (fun k => f (succ k)) n))` — peels the FRONT
    /// term off a finite product (`prodRange_succ` already peels the BACK term
    /// for free). Induction on `n`, mirroring `Nat.sumRange_shiftFront`'s own
    /// proof shape (`nat_prelude/binomial.rs::declare_sum_range_shift_front`)
    /// with `Int.mul`/`mul_assoc` in place of `Nat.add`/`add_assoc` — and,
    /// unlike that Nat proof, the base case needs an explicit `mul_one`/
    /// `one_mul` pair rather than a single `zero_add`, since `Int.mul` does not
    /// reduce definitionally on a symbolic argument the way `Nat.add` does.
    /// Built for `wilson.rs`'s reindex of the interior product over
    /// `Nat.inverseIndex`'s two fixed points.
    pub prod_range_shift_front: NameId,
    /// `prodRange_split : ∀ f a b, Eq Int (prodRange f (add a b))
    ///   (mul (prodRange f a) (prodRange (fun k => f (add a k)) b))` — splits a
    /// finite product at a SYMBOLIC point. [`Self::prod_range_shift_front`]
    /// peels one term off the front and [`Self::prod_range_succ`] one off the
    /// back; neither cuts the range in two at an arbitrary index, which is what
    /// a reflection argument over `[0,2m)` needs (ADR-1230's handoff for the
    /// first supplementary law's residue half). Induction on `b`; no
    /// `Nat.add_assoc` anywhere, because `Nat.add` recurses on its RIGHT
    /// argument so `add a (succ j)` iota-reduces to `succ (add a j)`.
    /// `prod.rs::declare_prod_range_split`.
    pub prod_range_split: NameId,
    /// `prodRange_congr : ∀ f g n, (∀ k, Eq Int (f k) (g k)) → Eq Int (prodRange f n) (prodRange g n)`
    /// — pointwise-equal factors give equal products, by induction on `n`.
    pub prod_range_congr: NameId,
    /// `prodRange_congr_lt : ∀ f g n, (∀ k, Lt k n → Eq Int (f k) (g k)) →
    /// Eq Int (prodRange f n) (prodRange g n)` — `prod_range_congr` with the
    /// hypothesis weakened to indices below the bound (mirrors
    /// `Nat.sumRange_congr_lt`), which is what `prodRange_swap_adjacent`'s base
    /// case actually has (agreement everywhere *except* two points, which
    /// `prodRange f i`/`prodRange g i` never reach).
    pub prod_range_congr_lt: NameId,
    /// `prodRange_swap_adjacent :
    ///   ∀ f g i n, Lt (succ i) n → Eq Int (g i) (f (succ i)) →
    ///     Eq Int (g (succ i)) (f i) →
    ///     (∀ k, Not (Eq Nat k i) → Not (Eq Nat k (succ i)) → Eq Int (f k) (g k)) →
    ///     Eq Int (prodRange f n) (prodRange g n)`
    /// — swapping `f`'s values at one adjacent pair of indices, with `g`
    /// supplied (not computed) and agreeing with `f` everywhere else, leaves
    /// the product unchanged: the transposition case of permutation
    /// invariance (`docs`/the finite-index brief), and the germ of
    /// `prodRange_permute`. `g` is a parameter rather than a computed
    /// swap-function specifically so the proof needs no decidable-equality
    /// machinery — see `prod.rs`'s doc comment on
    /// `declare_prod_range_swap_adjacent`.
    pub prod_range_swap_adjacent: NameId,
    /// `prodRange_swap :
    ///   ∀ f g i j n, Lt i j → Lt j n → Eq Int (g i) (f j) →
    ///     Eq Int (g j) (f i) →
    ///     (∀ k, Not (Eq Nat k i) → Not (Eq Nat k j) → Eq Int (f k) (g k)) →
    ///     Eq Int (prodRange f n) (prodRange g n)`
    /// — the general transposition (any `i < j`, not just adjacent): stated
    /// the way `prod_range_swap_adjacent` is (`g` supplied by hypothesis), by
    /// `Nat.le_dest` + an auxiliary induction that conjugates through
    /// `(j' j)(i j')(j' j) = (i j)` using `prod.rs`'s `point_swap` — see
    /// `declare_prod_range_swap`'s doc comment for the full route.
    pub prod_range_swap: NameId,
    /// `prodRange_permute :
    ///   ∀ f σ n, InjectiveOn σ n → MapsInto σ n →
    ///     Eq Int (prodRange f n) (prodRange (fun k => f (σ k)) n)`
    /// — the general permutation: any `InjectiveOn`/`MapsInto` self-map of
    /// `{0,…,n-1}` rearranges the product without changing its value.
    /// Induction on `n` with `f` fixed and the motive generalized over `σ`;
    /// at `succ n` the pigeonhole (`Nat.injective_on_imp_surjective_on`)
    /// locates `i0` with `σ i0 = n`, then either bound-weakens (`i0 = n`) or
    /// applies `prodRange_swap` plus `Nat.restrict_injective`/
    /// `Nat.restrict_maps_into`'s override (`i0 < n`) — see `prod.rs`'s
    /// module doc above `declare_prod_range_permute` for the full route.
    pub prod_range_permute: NameId,
    /// `prodRange_mul :
    ///   ∀ f g n, Eq Int (prodRange (fun k => mul (f k) (g k)) n)
    ///     (mul (prodRange f n) (prodRange g n))` — a product of pointwise
    /// products is the product of the two products. Induction on `n`,
    /// closing the successor step with a `mul_assoc`/`mul_comm`
    /// rearrangement of the four factors (`prod.rs`'s `mul_swap_inner`).
    pub prod_range_mul: NameId,
    /// `prodRange_const_pow : ∀ a n, Eq Int (prodRange (fun _ => a) n) (pow a n)`
    /// — a product of `n` copies of one factor is that factor to the `n`th
    /// power. `prod.rs::declare_prod_range_const_pow`.
    pub prod_range_const_pow: NameId,
    /// `prodRange_scaledIndexEqPowMulFactorial : ∀ a m, Eq Int (prodRange
    ///   (fun k => mul a (ofNat (succ k))) m) (mul (pow a m) (factorial m))`
    /// -- ADR-0990's Gauss's-lemma item A: `∏(a·k) = a^m·m!`.
    /// `gauss_factorial_product.rs`.
    pub prod_range_scaled_index_eq_pow_mul_factorial: NameId,
    /// `prodRangeIf : (Nat → Bool) → (Nat → Int) → Nat → Int := fun pred f n
    ///   => prodRange (fun i => bool_select_int (pred i) (f i) one) n` — the
    /// `Int` counterpart of `Nat.prodRangeIf`
    /// (`nat_prelude/subset_product.rs`): a product folded over a
    /// predicate-defined subset of `[0,n)`. See `euler_theorem.rs`'s module
    /// doc for why this lives over `Int` rather than `Nat`.
    pub prod_range_if: NameId,
    /// `prodRangeIf_zero : ∀ pred f, Eq Int (prodRangeIf pred f zero) one` —
    /// closes by `Eq.refl`.
    pub prod_range_if_zero: NameId,
    /// `prodRangeIf_succ : ∀ pred f n, Eq Int (prodRangeIf pred f (succ n))
    ///   (mul (prodRangeIf pred f n) (bool_select_int (pred n) (f n) one))`
    /// — closes by `Eq.refl`.
    pub prod_range_if_succ: NameId,
    /// `prodRangeIf_permute :
    ///   ∀ pred f σ n, InjectiveOn σ n → MapsInto σ n →
    ///     (∀ i, Lt i n → Eq Bool (pred (σ i)) (pred i)) →
    ///     Eq Int (prodRangeIf pred f n) (prodRangeIf pred (fun k => f (σ k)) n)`
    /// — a predicate-restricted product is invariant under any
    /// `InjectiveOn`/`MapsInto` self-map of `[0,n)` that additionally
    /// preserves the predicate on that range. Derived from
    /// `prodRange_permute` (full-range invariance) plus `prodRange_congr_lt`
    /// — see `euler_theorem.rs`'s module doc for the route and for the
    /// precise remaining gap to Euler's totient theorem.
    pub prod_range_if_permute: NameId,
    /// `gaussSignProdEqPowNegOneOfCount : ∀ pp a m, Eq Int (prodRange (fun j
    ///   => bool_select_int (Nat.gaussSignNeg pp a (succ j)) (neg one) one)
    ///   m) (pow (neg one) (Nat.gaussNegCount pp a m))` -- Gauss's lemma's
    /// sign-product identity, a one-line corollary of
    /// `prod_range_if_const_eq_pow_count`. `gauss_sign_product.rs`.
    pub gauss_sign_prod_eq_pow_neg_one_of_count: NameId,
    /// `factorialEqOfNatFactorial : ∀ m, Eq Int (factorial m) (ofNat
    ///   (Nat.factorial m))` — item 2 of the connecting theorem (ADR-1070):
    /// bridges `Int.factorial` (this prelude's `prodRange`-built version)
    /// with `Nat.factorial`, by induction. `gauss_factorial_coprime.rs`.
    pub factorial_eq_of_nat_factorial: NameId,
    /// `coprimeFactorialOfLtPrime : ∀ pp m, Nat.PrimeCond pp → Lt m pp →
    ///   Coprime (factorial m) (ofNat pp)` — item 2 of the connecting
    /// theorem (ADR-1070), the `Int`-typed form `Int.ModEq.cancel` needs in
    /// item 3's final assembly. `gauss_factorial_coprime.rs`.
    pub coprime_factorial_of_lt_prime: NameId,
    /// `gaussTermModEq : ∀ pp a k, Lt zero pp →
    ///   ModEq (ofNat pp) (mul (ofNat a) (ofNat k))
    ///     (mul (bool_select_int (Nat.gaussSignNeg pp a k) (neg one) one)
    ///          (ofNat (Nat.gaussFold pp a k)))` -- item 1 of Gauss's-lemma
    /// connecting theorem (ADR-1070/ADR-1130): the per-term congruence, one
    /// factor of the product the final assembly folds.
    /// `gauss_term_congruence.rs`.
    pub gauss_term_mod_eq: NameId,
    /// `gaussLemmaSignCount : ∀ m a, Nat.PrimeCond (succ (mul 2 m)) →
    ///   Eq Nat (gcd a (succ (mul 2 m))) one →
    ///   ModEq (ofNat (succ (mul 2 m))) (pow (ofNat a) m)
    ///     (pow (neg one) (Nat.gaussNegCount (succ (mul 2 m)) a m))`
    /// — **Gauss's lemma** (the quadratic-residue one), the connecting
    /// theorem ADR-0990 sized in five pieces and ADR-1070 reduced to two.
    /// `gauss_assembly.rs`.
    ///
    /// NOT to be confused with [`Self::gauss_lemma`], which despite its name
    /// is EUCLID's lemma (`Coprime a b → a ∣ b*c → a ∣ c`) — the same
    /// misnomer `Nat.gauss_lemma` carries, and the reason this declaration is
    /// spelled out rather than taking the bare name.
    pub gauss_lemma_sign_count: NameId,

    // --- the second supplementary law of quadratic reciprocity (ADR-1150) ---
    /// `Int.pow_neg_one_of_even : ∀ (n : Nat), Nat.Even n →
    ///   Eq Int (pow (neg one) n) one` (`second_supplementary.rs`).
    pub pow_neg_one_of_even: NameId,
    /// `Int.pow_neg_one_of_odd : ∀ (n : Nat), Nat.Odd n →
    ///   Eq Int (pow (neg one) n) (neg one)` (`second_supplementary.rs`).
    pub pow_neg_one_of_odd: NameId,
    /// `Int.secondSupplementaryLaw : ∀ m, Nat.PrimeCond (succ (mul 2 m)) →`
    /// `  Or (And <p = 8q+1 or 8q+7> (ModEq (ofNat p) (pow (ofNat 2) m) one))`
    /// `     (And <p = 8q+3 or 8q+5> (ModEq (ofNat p) (pow (ofNat 2) m) (neg one)))`
    /// — **the second supplementary law of quadratic reciprocity** in its
    /// Legendre-symbol form: for an odd prime `p = 2m+1`,
    /// `2^((p-1)/2) ≡ 1 [p]` exactly when `p ≡ ±1 (mod 8)` and `≡ -1` exactly
    /// when `p ≡ ±3 (mod 8)`. The four `m`-shapes are exhaustive and mutually
    /// exclusive, so this single disjunction gives both directions of each
    /// line. Over `Int.gaussLemmaSignCount` (ADR-1130),
    /// `Nat.gaussNegCountTwoClosedForm` and `Nat.half_ceil_parity`
    /// (ADR-1150). `second_supplementary.rs`.
    pub second_supplementary_law: NameId,

    // --- the first supplementary law of quadratic reciprocity (ADR-1230) ---
    /// `Int.isQuadraticResidue_of_modEq : ∀ (n a b : Int), ModEq n a b →
    ///   IsQuadraticResidue n a → IsQuadraticResidue n b` — quadratic-residue-
    /// hood respects `ModEq` in its second argument (the witness is unchanged;
    /// `Int.ModEq.trans` composes `x*x ≡ a` with `a ≡ b`). Needed because every
    /// quadratic-residue theorem in `qr_criterion.rs` is stated over a NATURAL
    /// representative `ofNat aa`, while the supplementary laws are about `-1`.
    /// `first_supplementary.rs`.
    pub is_quadratic_residue_of_mod_eq: NameId,
    /// `Int.wilsonHalfSplit : ∀ m, Nat.PrimeCond (succ (mul 2 m)) →
    ///   ModEq (ofNat (succ (mul 2 m)))
    ///     (mul (factorial m) (mul (pow (neg one) m) (factorial m))) (neg one)`
    /// — `(p-1)! = m! · ((-1)^m · m!)` mod `p`, for BOTH parities of `m`.
    /// Wilson's theorem split at `m` (`prodRange_split`), the upper half
    /// reversed by `prodRange_permute` at `k ↦ sub (pred m) k`, made congruent
    /// termwise to `(-1)·(k+1)`, and collapsed by
    /// [`Self::prod_range_scaled_index_eq_pow_mul_factorial`]. This is the
    /// witness supply the residue half of the first supplementary law needs,
    /// and it avoids the converse of Euler's criterion entirely.
    /// `first_supplementary_residue.rs`.
    pub wilson_half_split: NameId,
    /// `Int.firstSupplementaryLawResidue : ∀ m,
    ///   Nat.PrimeCond (succ (mul 2 m)) → Nat.Even m →
    ///   IsQuadraticResidue (ofNat (succ (mul 2 m))) (neg one)` — **the first
    /// supplementary law of quadratic reciprocity**, residue half: for an odd
    /// prime `p ≡ 1 (mod 4)`, `-1` IS a quadratic residue, witness
    /// `Int.factorial m`. Together with
    /// [`Self::first_supplementary_law_not_residue`] this is the whole law.
    /// `first_supplementary_residue.rs`.
    pub first_supplementary_law_residue: NameId,
    /// `Int.firstSupplementaryLawNotResidue : ∀ m,
    ///   Nat.PrimeCond (succ (mul 2 m)) → Nat.Odd m →
    ///   Not (IsQuadraticResidue (ofNat (succ (mul 2 m))) (neg one))`
    /// — **the first supplementary law of quadratic reciprocity, non-residue
    /// half**: for an odd prime `p = 2m+1` with `m` odd (equivalently
    /// `p ≡ 3 (mod 4)`), `-1` is not a quadratic residue mod `p`. Over
    /// `Int.euler_criterion_neg_one_imp_not_residue` at the natural
    /// representative `aa := 2*m`, transported back to `-1` along
    /// [`Self::is_quadratic_residue_of_mod_eq`].
    ///
    /// The converse half (`p ≡ 1 (mod 4) ⟹ -1 IS a residue`) is NOT proved:
    /// it needs a witness, and the Euler-criterion route to one requires the
    /// CONVERSE of Euler's criterion, which this prelude does not build. See
    /// `first_supplementary.rs`'s module doc for the Wilson-theorem route that
    /// avoids the converse and for the single `prodRange` split it still
    /// lacks.
    pub first_supplementary_law_not_residue: NameId,

    // --- discreteness and decision laws --------------------------------------
    /// `no_int_between : ∀ (x : Int), Not (And (lt zero x) (lt x one))`.
    pub no_int_between: NameId,
    /// `le_total : ∀ (a b : Int), Or (le a b) (le b a)`.
    pub le_total: NameId,
    /// `lt_of_le_of_ne :
    /// ∀ (a b : Int), le a b → Not (Eq Int a b) → lt a b`.
    pub lt_of_le_of_ne: NameId,
    /// `le_antisymm : ∀ (a b : Int), le a b → le b a → Eq Int a b` — proved
    /// through trichotomy (`eq_em`), not a sign case-split: split on whether
    /// `a = b` already, and in the disequality branch `lt_of_le_of_ne` gives
    /// both `lt a b` and `lt b a`, which `lt_trans` + `lt_irrefl` refute.
    pub le_antisymm: NameId,
    /// `euclidean_decomposition : ∀ t k, 0 < k → ∃ q r, t = k*q+r ∧ 0 ≤ r ∧ r < k`.
    pub euclidean_decomposition: NameId,
    /// `euclid_of_nat : ∀ n m, ∃ q r, ofNat n = ofNat (succ m)*q+r ∧ 0 ≤ r ∧ r < ofNat (succ m)`.
    ///
    /// The non-negative branch of [`Self::euclidean_decomposition`], stated over
    /// `ℕ` parameters so the divisor is positive by construction.
    pub euclid_of_nat: NameId,
    /// `euclid_neg_succ : ∀ n m, ∃ q r, negSucc n = ofNat (succ m)*q+r ∧ 0 ≤ r ∧ r < ofNat (succ m)`.
    ///
    /// The negative branch of [`Self::euclidean_decomposition`].
    pub euclid_neg_succ: NameId,

    // --- Euclidean ("E-rounding") division: `Int.ediv` / `Int.emod` ----------
    /// `Int.ediv : Int → Int → Int` — the Euclidean quotient, matching Lean 4
    /// core's `Int.ediv` (`Init.Data.Int.DivMod.Basic`) bit for bit: total,
    /// `ediv _ 0 = 0`, and for `b ≠ 0` the unique `q` with
    /// `0 ≤ (a - b*q) < |b|`. A checked structural `Int.rec` definition, not an
    /// axiom.
    pub ediv: NameId,
    /// `Int.emod : Int → Int → Int` — the Euclidean remainder,
    /// `emod a b = a - b * ediv a b`, matching Lean 4 core's `Int.emod`
    /// bit for bit: total, `emod a 0 = a`, and `0 ≤ emod a b < natAbs b` for
    /// `b ≠ 0`.
    pub emod: NameId,
    /// `ediv_add_emod : ∀ a b, b * (a / b) + a % b = a` — the division
    /// algorithm as an equation. The keystone: it turns `Int.ediv`/`Int.emod`
    /// from "some total functions" into "the Euclidean quotient and
    /// remainder", and is what `Int.ediv_emod_unique` would pin against.
    pub ediv_add_emod: NameId,
    /// `emod_nonneg : ∀ a b, Not (Eq Int b zero) → 0 ≤ a % b` — one of the two
    /// bounds that make the remainder canonical.
    pub emod_nonneg: NameId,
    /// `emod_lt_of_pos : ∀ a b, 0 < b → a % b < b` — the other bound that
    /// makes the remainder canonical.
    pub emod_lt_of_pos: NameId,
    /// `emod_natAbs_bound : ∀ a b, b ≠ 0 → a % b < ofNat (natAbs b)` — the
    /// sign-general analogue of [`Self::emod_lt_of_pos`]: `emod_lt_of_pos`
    /// bounds the remainder against `b` itself, which is only correct for
    /// `b > 0` (it is literally false for `b < 0`, since a `negSucc` is never
    /// an upper bound for a nonnegative remainder); the correct bound for
    /// EITHER sign is `natAbs b`. Keystone for any negative-divisor argument
    /// in this development (`F:ml430-int-gcd-div-5e01872f`'s missing piece).
    pub emod_natabs_bound: NameId,
    /// `ediv_emod_unique : ∀ a b q1 r1 q2 r2,
    /// 0 < b → a = b*q1+r1 → 0 ≤ r1 → r1 < b →
    /// a = b*q2+r2 → 0 ≤ r2 → r2 < b → q1 = q2 ∧ r1 = r2` — the division
    /// algorithm's uniqueness for a **positive** divisor: any two
    /// quotient/remainder pairs reconstructing the same dividend with
    /// remainders in `[0, b)` agree.
    pub ediv_emod_unique: NameId,
    /// `ediv_emod_unique_general : ∀ a b q1 r1 q2 r2,
    /// Not (Eq Int b zero) → a = b*q1+r1 → 0 ≤ r1 → r1 < ofNat (natAbs b) →
    /// a = b*q2+r2 → 0 ≤ r2 → r2 < ofNat (natAbs b) → q1 = q2 ∧ r1 = r2` —
    /// the sign-general analogue of [`Self::ediv_emod_unique`]: any divisor
    /// sign, bounding the remainder against `natAbs b` (as
    /// [`Self::emod_natabs_bound`] does) rather than `b` itself. For `b > 0`
    /// this is a direct application of `ediv_emod_unique` (`natAbs b`
    /// coincides with `b`); for `b < 0` it is `ediv_emod_unique` applied at
    /// the positive divisor `neg b`, with both quotients negated
    /// (`b*q = (neg b)*(neg q)`) and un-negated again on the way out.
    pub ediv_emod_unique_general: NameId,

    // --- divisibility: `Int.dvd a b := ∃ c, b = a * c` -----------------------
    /// `Int.dvd : Int → Int → Prop`, where `dvd a b := ∃ c, b = a * c`.
    pub dvd: NameId,
    /// `dvd_refl : ∀ a, dvd a a`.
    pub dvd_refl: NameId,
    /// `dvd_trans : ∀ a b c, dvd a b → dvd b c → dvd a c`.
    pub dvd_trans: NameId,
    /// `dvd_add : ∀ a m n, dvd a m → dvd a n → dvd a (m + n)`.
    pub dvd_add: NameId,
    /// `dvd_mul_right : ∀ a b, dvd a (a * b)`.
    pub dvd_mul_right: NameId,
    /// `dvd_mul_left : ∀ a b, dvd a (b * a)`.
    pub dvd_mul_left: NameId,
    /// `emod_eq_zero_iff_dvd : ∀ a b, 0 < b → (a % b = 0 ↔ b ∣ a)` — the
    /// bridge between `Int.ediv_emod_unique` and `Int.dvd`, for a positive
    /// divisor.
    pub emod_eq_zero_iff_dvd: NameId,
    /// `emod_eq_zero_iff_dvd_general : ∀ a b, b ≠ 0 → (a % b = 0 ↔ b ∣ a)` —
    /// the sign-general analogue of [`Self::emod_eq_zero_iff_dvd`], built the
    /// same way (`mp` from `Int.ediv_add_emod`, `mpr` from a uniqueness
    /// argument) but against [`Self::emod_natabs_bound`] and
    /// [`Self::ediv_emod_unique_general`] instead of their positive-only
    /// siblings, so it holds for a divisor of either sign. The keystone
    /// `F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`) needed and the prior
    /// `int-emod-negative` lane's handoff named but did not build.
    pub emod_eq_zero_iff_dvd_general: NameId,

    // --- congruence modulo `n`: `Int.ModEq n a b := emod a n = emod b n` ----
    /// `Int.ModEq : Int → Int → Int → Prop`.
    pub mod_eq: NameId,
    /// `ModEq.refl : ∀ n a, ModEq n a a`.
    pub mod_eq_refl: NameId,
    /// `ModEq.symm : ∀ n a b, ModEq n a b → ModEq n b a`.
    pub mod_eq_symm: NameId,
    /// `ModEq.trans : ∀ n a b c, ModEq n a b → ModEq n b c → ModEq n a c`.
    pub mod_eq_trans: NameId,
    /// `modEq_iff_dvd : ∀ n a b, 0 < n → (ModEq n a b ↔ n ∣ (b - a))` — the
    /// bridge from `ModEq` to `Int.dvd`, scoped to `0 < n` for the same reason
    /// [`Self::emod_eq_zero_iff_dvd`] is: no proved bound on `emod`'s magnitude
    /// for a negative modulus exists yet.
    pub mod_eq_iff_dvd: NameId,
    /// `modEq_of_nat_modEq : ∀ (d a b : Nat), Nat.modEq d a b → 0 < d →
    /// ModEq (ofNat d) (ofNat a) (ofNat b)` — transport a `Nat.modEq`
    /// congruence (balanced witnesses) into `Int.ModEq`, the ℕ→ℤ direction
    /// (the reverse needs `emod`'s magnitude bound for a witness pointing the
    /// other way, which is not what this route builds). The `0 < d`
    /// hypothesis is threaded through to `modEq_iff_dvd`, which needs it for
    /// the same reason every congruence in this module does.
    pub mod_eq_of_nat_mod_eq: NameId,
    /// `ModEq.add_right : ∀ n a b c, ModEq n a b → ModEq n (a+c) (b+c)`,
    /// UNCONDITIONAL in `n` (Mathlib's own statement carries no positivity
    /// hypothesis; the earlier `0 < n`-scoped proof here was a proof-route
    /// artifact of going through the positive-only half of
    /// [`Self::mod_eq_iff_dvd`], not a mathematical necessity — see
    /// `int_prelude/modeq.rs`'s `modeq_to_dvd`/`dvd_to_modeq`).
    pub mod_eq_add_right: NameId,
    /// `ModEq.add_left : ∀ n a b c, ModEq n a b → ModEq n (c+a) (c+b)`,
    /// UNCONDITIONAL in `n` — see [`Self::mod_eq_add_right`].
    pub mod_eq_add_left: NameId,
    /// `ModEq.add_left_cancel' : ∀ n a b c, ModEq n (c+a) (c+b) → ModEq n a b`,
    /// UNCONDITIONAL in `n`. Shift both sides by `-c` via
    /// [`Self::mod_eq_add_left`] and simplify.
    pub mod_eq_add_left_cancel: NameId,
    /// `ModEq.neg : ∀ n a b, ModEq n a b → ModEq n (-a) (-b)`, UNCONDITIONAL
    /// in `n`.
    pub mod_eq_neg: NameId,
    /// `neg_modEq_neg : ∀ n a b, ModEq n (-a) (-b) ↔ ModEq n a b`,
    /// UNCONDITIONAL in `n`.
    pub neg_mod_eq_neg: NameId,
    /// `ModEq.of_dvd : ∀ m n a b, dvd m n → ModEq n a b → ModEq m a b`,
    /// UNCONDITIONAL in both `m` and `n`.
    pub mod_eq_of_dvd: NameId,
    /// `ModEq.dvd_iff : ∀ n a b, ModEq n a b → (dvd n a ↔ dvd n b)`,
    /// UNCONDITIONAL in `n`.
    pub mod_eq_dvd_iff: NameId,
    /// `ModEq.of_mul_left : ∀ n a b m, ModEq (m*n) a b → ModEq n a b` — the
    /// special case of [`Self::mod_eq_of_dvd`] at `dvd n (m*n)`
    /// (`Int.dvd_mul_left`).
    pub mod_eq_of_mul_left: NameId,
    /// `ModEq.of_mul_right : ∀ n a b m, ModEq (n*m) a b → ModEq n a b` — the
    /// same special case of [`Self::mod_eq_of_dvd`] at the mirrored witness
    /// `dvd n (n*m)` (`Int.dvd_mul_right`).
    pub mod_eq_of_mul_right: NameId,
    /// `ModEq.mul_left : ∀ n a b c, 0 < n → ModEq n a b → ModEq n (c*a) (c*b)`
    /// — the primitive multiplicative congruence.
    pub mod_eq_mul_left: NameId,
    /// `ModEq.mul_right : ∀ n a b c, 0 < n → ModEq n a b → ModEq n (a*c) (b*c)`
    /// — derived from [`Self::mod_eq_mul_left`] by commuting.
    pub mod_eq_mul_right: NameId,
    /// `ModEq.mul :
    /// ∀ n a b c e, 0 < n → ModEq n a b → ModEq n c e → ModEq n (a*c) (b*e)`
    /// — the two-sided multiplicative congruence.
    pub mod_eq_mul: NameId,
    /// `modEq_cancel :
    /// ∀ n c a b, 0 < n → Coprime c n → ModEq n (c*a) (c*b) → ModEq n a b` —
    /// cancellation, via [`Self::gauss_lemma`].
    pub mod_eq_cancel: NameId,
    /// `modEq_inverse_exists :
    /// ∀ n a, 0 < n → Coprime a n → ∃ b, ModEq n (a*b) one` — the modular
    /// inverse, straight from Bézout ([`Self::gcd_eq_gcd_ab`]).
    pub mod_eq_inverse_exists: NameId,
    /// `modEq_inverse_unique :
    /// ∀ n a b c, 0 < n → ModEq n (a*b) one → ModEq n (a*c) one → ModEq n b c`
    /// — *the* inverse mod `n` is unique up to `ModEq`: `b` and `c` are both
    /// forced to agree with it. `Coprime a n` is not an extra hypothesis —
    /// it is derived from `ModEq n (a*b) one` itself (the divisibility
    /// witness `n ∣ (one - a*b)` unpacks to a Bézout certificate for `a`
    /// and `n`, closed by [`Self::coprime_of_bezout_one`]), then
    /// [`Self::mod_eq_cancel`] finishes from `ModEq n (a*b) (a*c)`.
    pub mod_eq_inverse_unique: NameId,
    /// `modEq_pow : ∀ n a b k, 0 < n → ModEq n a b → ModEq n (pow a k) (pow b k)`
    /// — induction on `k`, using [`Self::mod_eq_mul`] at each step. `k` is a
    /// `Nat` (the exponent), so this quantifies over three `Int`s and one
    /// `Nat` and is declared by hand rather than through
    /// `ops::IntDev::int_theorem`.
    pub mod_eq_pow: NameId,
    /// `modEq_prodRange :
    /// ∀ n f g m, 0 < n → (∀ k, ModEq n (f k) (g k)) →
    ///   ModEq n (prodRange f m) (prodRange g m)`
    /// — a product reduces modulo `n` factor by factor. Induction on `m`,
    /// using [`Self::mod_eq_mul`] at each step — [`Self::mod_eq_pow`] is the
    /// special case where `f`/`g` are the constant functions `pow` folds.
    /// Quantifies over one `Int`, two `Nat → Int` functions and one `Nat`, so
    /// this is declared by hand rather than through
    /// `ops::IntDev::int_theorem`.
    pub mod_eq_prod_range: NameId,
    /// `modEq_sumRange : ∀ n f g m, (∀ k, ModEq n (f k) (g k)) →
    /// ModEq n (sumRange f m) (sumRange g m)` — a finite sum reduces modulo
    /// `n` term by term. **UNCONDITIONAL in `n`**, unlike
    /// [`Self::mod_eq_prod_range`]: the step goes through
    /// [`Self::mod_eq_add_right`]/[`Self::mod_eq_add_left`], which this prelude
    /// proves without a positivity hypothesis, where the product's step needs
    /// the positivity-scoped [`Self::mod_eq_mul`]. `sum.rs`.
    pub mod_eq_sum_range: NameId,
    /// `modEq_prodRange_lt :
    /// ∀ n f g m, 0 < n → (∀ k, Lt k m → ModEq n (f k) (g k)) →
    ///   ModEq n (prodRange f m) (prodRange g m)` — [`Self::mod_eq_prod_range`]'s
    /// pointwise hypothesis weakened to indices below the bound, mirroring
    /// [`Self::prod_range_congr_lt`]'s own weakening of `prod_range_congr`.
    /// Needed because a per-index congruence built from
    /// [`Self::mul_inv_of_pow`] only holds for indices inside a bounded range
    /// (`0 < a`, `a < p`), so the unrestricted `mod_eq_prod_range` cannot be
    /// fed it directly.
    pub mod_eq_prod_range_lt: NameId,
    /// `emod_neg : ∀ a n, emod a (neg n) = emod a n` — negating the modulus
    /// leaves `emod` unchanged. Purely structural (which `Int.rec` branch of
    /// `emod`'s own definition a shape of `n` selects), so unlike
    /// [`Self::mod_eq_iff_dvd`] it needs no positivity hypothesis at all —
    /// see `int_prelude/modeq_family.rs`.
    pub emod_neg: NameId,
    /// `modEq_of_neg_modulus : ∀ n a b, ModEq (neg n) a b → ModEq n a b` —
    /// the `mp` half of the ledger's `Int.modEq_neg` row (no `Iff` in this
    /// kernel), via [`Self::emod_neg`].
    pub mod_eq_of_neg_modulus: NameId,
    /// `modEq_neg_modulus : ∀ n a b, ModEq n a b → ModEq (neg n) a b` — the
    /// `mpr` half.
    pub mod_eq_neg_modulus: NameId,
    /// `modEq_one : ∀ a b, ModEq one a b` — every integer is congruent mod
    /// `1`, via the existing positive-divisor bridge at the concrete literal
    /// `n = 1`.
    pub mod_eq_one: NameId,
    /// `modEq_add_mul_left : ∀ n a q, ModEq n (add (mul n q) a) a` — adding
    /// any multiple of the modulus leaves the residue unchanged, for **every**
    /// `n : ℤ` including `n = 0` and negative `n`. Unlike
    /// [`Self::mod_eq_iff_dvd`] and everything built on it in
    /// `int_prelude/modeq.rs`, this needs no `0 < n` hypothesis: the
    /// `n = 0` case is direct (`Int.emod _ 0` is the identity), the positive
    /// case goes through the existing bridge at the concrete shape
    /// `ofNat (succ k)`, and the negative case reduces to the positive one via
    /// [`Self::mod_eq_neg_modulus`] — see `int_prelude/modeq_family.rs`.
    pub mod_eq_add_mul_left: NameId,
    /// `add_modEq_left : ∀ n a, ModEq n (add n a) a` — Mathlib's
    /// `Int.add_modEq_left`, unconditional in `n`. [`Self::mod_eq_add_mul_left`]
    /// at `q := 1`.
    pub add_mod_eq_left: NameId,
    /// `add_modEq_right : ∀ n a, ModEq n (add a n) a` — Mathlib's
    /// `Int.add_modEq_right`, unconditional in `n`.
    pub add_mod_eq_right: NameId,
    /// `mod_modEq : ∀ a n, ModEq n (emod a n) a` — Mathlib's `Int.mod_modEq`
    /// (`a % n ≡ a [ZMOD n]`), unconditional in `n`, via
    /// [`Self::mod_eq_add_mul_left`] and [`Self::ediv_add_emod`].
    pub mod_mod_eq: NameId,
    /// `modulus_modEq_zero : ∀ n, ModEq n n zero` (`n ≡ 0 [ZMOD n]`),
    /// unconditional in `n`.
    pub modulus_mod_eq_zero: NameId,
    /// `modEq_sub : ∀ a b, ModEq (sub a b) a b` (`a ≡ b [ZMOD a - b]`),
    /// unconditional in `a, b`.
    pub mod_eq_sub: NameId,
    /// `natAbs : Int → Nat` — the magnitude, `ofNat n ↦ n` and `negSucc m ↦ succ m`.
    pub nat_abs: NameId,
    /// `of_nat_nat_abs_of_nonneg : ∀ a, 0 ≤ a → ofNat (natAbs a) = a`.
    pub of_nat_nat_abs_of_nonneg: NameId,
    /// `nat_abs_neg_of_nat : ∀ k, natAbs (negOfNat k) = k` — the magnitude of a
    /// negated natural is that natural.
    pub nat_abs_neg_of_nat: NameId,
    /// `nat_abs_neg : ∀ n, natAbs (neg n) = natAbs n` — negation preserves
    /// magnitude.
    pub nat_abs_neg: NameId,
    /// `nat_abs_pow : ∀ a k, Eq Nat (natAbs (pow a k)) (Nat.pow (natAbs a)
    /// k)` — the magnitude of a power is the power of the magnitude.
    pub nat_abs_pow: NameId,

    // --- `Int.gcd`, Euclid's Book VII transported from `ℕ` -------------------
    /// `Int.gcd a b := Nat.gcd (natAbs a) (natAbs b)` — a `Nat`-valued gcd, as
    /// in Mathlib.
    pub gcd: NameId,
    /// `nat_abs_mul : ∀ a b, natAbs (a*b) = natAbs a * natAbs b` — the
    /// multiplicativity of `natAbs` the sign bridges below rest on.
    pub nat_abs_mul: NameId,
    /// `dvd_of_nat_abs_dvd : ∀ (x y : Int), natAbs x ∣ natAbs y → x ∣ y` — a
    /// `Nat` divisibility of two magnitudes lifts to `Int` divisibility of the
    /// signed values, **regardless of either side's sign**. The general form
    /// of the bridge the ℤ gcd development needs; `gcd_dvd_left`/
    /// `gcd_dvd_right` and the closing step of `dvd_gcd` are both instances of
    /// it.
    pub dvd_of_nat_abs_dvd: NameId,
    /// `nat_abs_dvd_nat_abs_of_dvd : ∀ a b, a ∣ b → natAbs a ∣ natAbs b` — the
    /// reverse bridge, feeding `Nat.dvd_gcd` from `Int.dvd` hypotheses.
    pub nat_abs_dvd_nat_abs_of_dvd: NameId,
    /// `gcd_dvd_left : ∀ a b, ofNat (gcd a b) ∣ a`.
    pub gcd_dvd_left: NameId,
    /// `gcd_dvd_right : ∀ a b, ofNat (gcd a b) ∣ b`.
    pub gcd_dvd_right: NameId,
    /// `gcd_comm : ∀ a b, Eq Nat (gcd a b) (gcd b a)` — proved by mutual
    /// `Nat.dvd_gcd`/`Nat.gcd_dvd_left`/`Nat.gcd_dvd_right` plus a general
    /// antisymmetry of `Nat.dvd` this development had not needed before
    /// (`Nat.le_of_dvd` + `Nat.one_le_of_dvd_pos` + `Nat.le_antisymm`, zero
    /// case by `Nat.zero_mul`), not by re-deriving Euclid's algorithm.
    pub gcd_comm: NameId,
    /// `gcd_one_right : ∀ a, Eq Nat (gcd a one) one` — `ofNat (gcd a 1) ∣ 1`
    /// (`gcd_dvd_right`) is already a `Nat` divisor of `1`, so
    /// `Nat.eq_one_of_dvd_one` closes it directly.
    pub gcd_one_right: NameId,
    /// `gcd_zero_right : ∀ a, Eq Nat (gcd a zero) (natAbs a)` — `gcd a 0`
    /// divides `natAbs a` (`gcd_dvd_left`) and `natAbs a` divides `gcd a 0`
    /// (`Nat.dvd_gcd` from `Nat.dvd_refl`/`Nat.dvd_zero`), closed by the same
    /// `Nat.dvd` antisymmetry `gcd_comm` uses.
    pub gcd_zero_right: NameId,
    /// `dvd_gcd : ∀ c a b, c ∣ a → c ∣ b → c ∣ ofNat (gcd a b)` — together with
    /// `gcd_dvd_left`/`gcd_dvd_right`, the universal property that makes `gcd`
    /// *the* greatest common divisor.
    pub dvd_gcd: NameId,
    /// `ne_zero_of_gcd : ∀ x y, Eq Nat (gcd x y) zero → False → x ≠ 0 ∨ y ≠ 0`,
    /// i.e. `gcd x y ≠ 0 → x ≠ 0 ∨ y ≠ 0` — mirrors `Int.ne_zero_of_gcd`.
    /// `eq_em x 0` splits on whether `x = 0`; the `x ≠ 0` branch is
    /// immediate (`Or.inl`), and the `x = 0` branch derives `y ≠ 0` as a
    /// direct lambda: assuming `y = 0` too, `gcd_zero_right 0` (`gcd 0 0 =
    /// natAbs 0`, defeq `0`) transported along both equalities gives
    /// `gcd x y = 0`, contradicting the hypothesis.
    pub ne_zero_of_gcd: NameId,
    /// `gcd_eq_one_of_gcd_mul_right_eq_one_left : ∀ a m n, Eq Nat (gcd a
    /// (↑m*↑n)) one → Eq Nat (gcd a ↑m) one` — mirrors
    /// `Int.gcd_eq_one_of_gcd_mul_right_eq_one_left`. `Int.mul (ofNat m)
    /// (ofNat n)` reduces to `ofNat (m*n)` by ι-reduction (`define_binary_int`'s
    /// ofNat/ofNat branch), so both sides unfold to plain `Nat.gcd` statements;
    /// `Nat.dvd_mul` gives `m ∣ m*n`, and `Nat.coprime_of_dvd_right` closes it.
    pub gcd_eq_one_of_gcd_mul_right_eq_one_left: NameId,
    /// `gcd_eq_one_of_gcd_mul_right_eq_one_right : ∀ a m n, Eq Nat (gcd a
    /// (↑m*↑n)) one → Eq Nat (gcd a ↑n) one` — the right-hand mirror of
    /// [`gcd_eq_one_of_gcd_mul_right_eq_one_left`](Self::gcd_eq_one_of_gcd_mul_right_eq_one_left).
    /// `Nat.dvd_mul` gives `n ∣ n*m`, transported to `n ∣ m*n` by
    /// `Nat.mul_comm`, then `Nat.coprime_of_dvd_right` closes it.
    pub gcd_eq_one_of_gcd_mul_right_eq_one_right: NameId,
    /// `dvd_mul_split : ∀ c a b, Iff (dvd c (mul a b)) (∃ c1 c2, And (dvd c1
    /// a) (And (dvd c2 b) (Eq Int (mul c1 c2) c)))` — Mathlib's `Int.dvd_mul`
    /// (`F:ml430-int-dvd-mul-3a7b94cd`), the ℤ sibling of
    /// `Nat.dvd_mul_split`. Not named `Int.dvd_mul` for the same reason the
    /// `Nat` mirror isn't (`dvd_mul_split.rs`).
    pub dvd_mul_split: NameId,
    /// `gcd_eq_gcd_ab : ∀ a b, ∃ u v, ofNat (gcd a b) = a*u + b*v` — Bézout's
    /// identity over `ℤ` (Elements VII.2, strong form), transported from
    /// `Nat.gcd_bezout` through `natAbs`.
    pub gcd_eq_gcd_ab: NameId,

    // --- Bézout at named computable witnesses (`bezout_witnesses.rs`) --------
    /// `Nat.xgcdAux : Nat → Nat → Nat → Bool → Int` — the extended Euclidean
    /// recursion, structural on a **fuel** argument (never `WellFounded`, which
    /// would drag `propext`/`Quot.sound` in). The trailing `Bool` selects which
    /// of the two coefficients to return, so one recursion carries the pair
    /// without a product type — the same device `Nat.divModState` uses. All
    /// three equations are definitional; see `bezout_witnesses.rs`'s module doc.
    pub xgcd_aux: NameId,
    /// `Nat.gcdA : Nat → Nat → Int := fun m n => xgcdAux m m n true` — the
    /// Bézout coefficient of `m`, as a `Definition` that returns data (contrast
    /// [`Self::gcd_eq_gcd_ab`], whose witnesses are sealed inside a `Prop`).
    /// The fuel is `m` itself, which always suffices: see the module doc.
    pub nat_gcd_a: NameId,
    /// `Nat.gcdB : Nat → Nat → Int := fun m n => xgcdAux m m n false` — the
    /// Bézout coefficient of `n`.
    pub nat_gcd_b: NameId,
    /// `Nat.xgcdAux_sound : ∀ f m n, Nat.le m f →
    /// Eq Int (ofNat (Nat.gcd m n)) (ofNat m * xgcdAux f m n true +
    /// ofNat n * xgcdAux f m n false)` — Bézout for the fuelled recursion,
    /// by induction on the fuel with `m` and `n` generalized in the motive.
    pub xgcd_aux_sound: NameId,
    /// `Nat.gcd_eq_gcd_ab : ∀ m n, Eq Int (ofNat (Nat.gcd m n))
    /// (ofNat m * Nat.gcdA m n + ofNat n * Nat.gcdB m n)` —
    /// [`Self::xgcd_aux_sound`] at `f := m`, i.e. Bézout at the named
    /// coefficients over `ℕ`.
    pub nat_gcd_eq_gcd_ab: NameId,
    /// `Nat.exists_mul_mod_eq_gcd : ∀ n k, Nat.lt (Nat.gcd n k) k →
    /// ∃ m, Nat.lt m k ∧ Eq Nat (Nat.mod (Nat.mul n m) k) (Nat.gcd n k)` —
    /// Mathlib v4.30's `Nat.exists_mul_mod_eq_gcd`. Reduces the Bézout
    /// coefficient [`Self::nat_gcd_a`] modulo `k` to land a genuine `Nat`
    /// witness in `[0, k)`; see `gcd.rs`'s
    /// `declare_exists_mul_mod_eq_gcd` for the derivation.
    pub exists_mul_mod_eq_gcd: NameId,
    /// `Int.gcdA : Int → Int → Int` — Mathlib's signed coefficient of the
    /// first argument, a computable `Int.rec` on that argument that negates
    /// the `Nat` coefficient under `negSucc`.
    pub gcd_a: NameId,
    /// `Int.gcdB : Int → Int → Int` — the coefficient of the **second**
    /// argument, so its `Int.rec` splits on that argument instead.
    pub gcd_b: NameId,
    /// `gcd_eq_gcd_ab_witnesses : ∀ x y, Eq Int (ofNat (gcd x y))
    /// (x * gcdA x y + y * gcdB x y)` — Mathlib v4.30's
    /// `Int.gcd_eq_gcd_ab` verbatim, at the *named computable* witnesses.
    /// [`Self::gcd_eq_gcd_ab`] keeps the older existential name because
    /// `crt.rs` and `modinv.rs` consume that form.
    pub gcd_eq_gcd_ab_witnesses: NameId,
    /// `gcd_div_gcd_div_gcd : ∀ i j, Nat.lt zero (gcd i j) →
    /// Eq Nat (gcd (i.ediv (ofNat (gcd i j))) (j.ediv (ofNat (gcd i j)))) one`
    /// — Mathlib v4.30's `Int.gcd_div_gcd_div_gcd`: dividing both operands by
    /// their own gcd leaves a coprime pair. An independent Bézout route (see
    /// `int_prelude/gcd.rs`'s `declare_gcd_div_gcd_div_gcd`), not a corollary
    /// of `Int.gcd_div` (not proved here for a general, possibly negative,
    /// divisor).
    pub gcd_div_gcd_div_gcd: NameId,
    /// `gcd_div : ∀ a b c, c ∣ a → c ∣ b →
    /// Eq Nat (gcd (a.ediv c) (b.ediv c)) (Nat.div (gcd a b) (natAbs c))` —
    /// Mathlib v4.30's `Int.gcd_div` (alias of Lean 4 core's `Int.gcd_ediv`,
    /// `Init.Data.Int.Gcd`), for a divisor `c` of **either sign, or zero**.
    /// Closes `F:ml430-int-gcd-div-5e01872f`. Proved by mutual divisibility,
    /// NOT by transporting `Nat.gcd_mul_left` (that lemma does not exist in
    /// this development and would need a fresh Euclidean-recursion induction
    /// to build): with `qa := a.ediv c`, `qb := b.ediv c`, `C := natAbs c`,
    /// `G := gcd a b`, `H := gcd qa qb`, `c ≠ 0` reduces to showing
    /// `C*H = G`. `H ∣ G/C` follows from Bézout on `a,b` (`G`'s witnesses,
    /// scaled by `c`, show `ofNat(G/C) = ±(qa*u+qb*v)` up to sign, and `H`
    /// divides that sum termwise). `G/C ∣ H` follows from Bézout on `qa,qb`
    /// (`H`'s witnesses give `c*H = a*u'+b*v'`, which `G` divides, so
    /// `G ∣ C*H`, cancel the shared positive factor `C`). `Nat.dvd_antisymm`
    /// closes it. `c = 0` is separate and degenerate (`c∣a → a=0`, `c∣b →
    /// b=0`, both sides collapse to `0` via `gcd_zero_right`/`Nat.div_zero`).
    /// <!-- absent: Nat.gcd_mul_left -->
    pub gcd_div: NameId,
    /// `Int.Coprime a b := Eq Nat (gcd a b) 1` — the converse of Bézout
    /// (Elements VII, Def. 12), stated over the `Nat`-valued `gcd`.
    pub coprime: NameId,
    /// `coprime_of_bezout_one : ∀ a b u v, Eq Int (a*u+b*v) one → Coprime a b`.
    pub coprime_of_bezout_one: NameId,
    /// `gauss_lemma : ∀ a b c, Coprime a b → a ∣ (b*c) → a ∣ c` — Elements
    /// VII.30's engine; `euclid_lemma` is its corollary once `a` is prime.
    pub gauss_lemma: NameId,
    /// `dvd_of_dvd_mul_right_of_gcd_one : ∀ a b c,
    /// a ∣ (b*c) → Eq Nat (gcd a b) 1 → a ∣ c` — Mathlib v4.30's
    /// `Int.dvd_of_dvd_mul_right_of_gcd_one`, exactly [`Self::gauss_lemma`]
    /// with its two hypotheses reordered (`Eq Nat (gcd a b) 1` is `Coprime a
    /// b` unfolded).
    pub dvd_of_dvd_mul_right_of_gcd_one: NameId,
    /// `dvd_of_dvd_mul_left_of_gcd_one : ∀ a b c,
    /// a ∣ (b*c) → Eq Nat (gcd a c) 1 → a ∣ b` — Mathlib v4.30's
    /// `Int.dvd_of_dvd_mul_left_of_gcd_one`: [`Self::gauss_lemma`] applied at
    /// `(a, c, b)`, after rewriting `a ∣ (b*c)` to `a ∣ (c*b)` by
    /// `Int.mul_comm`.
    pub dvd_of_dvd_mul_left_of_gcd_one: NameId,
    /// `gcd_greatest : ∀ a b d, 0 ≤ d → d ∣ a → d ∣ b →
    /// (∀ e, e ∣ a → e ∣ b → e ∣ d) → Eq Int d (ofNat (gcd a b))` — Mathlib
    /// v4.30's `Int.gcd_greatest`. Both directions come from the universal
    /// property already proved ([`Self::gcd_dvd_left`]/[`Self::gcd_dvd_right`]/
    /// [`Self::dvd_gcd`]): `d ∣ ofNat (gcd a b)` is `dvd_gcd` fed `d`'s own
    /// hypotheses directly, and `ofNat (gcd a b) ∣ d` is the universal
    /// hypothesis fed `gcd_dvd_left`/`gcd_dvd_right`. Mutual `Int.dvd` plus
    /// `0 ≤ d` closes by `natAbs`-level antisymmetry (the same private engine
    /// `gcd_comm`/`gcd_zero_right` already use) and
    /// [`Self::of_nat_nat_abs_of_nonneg`].
    pub gcd_greatest: NameId,
    /// `euclid_lemma : ∀ p a b,
    /// (2 ≤ natAbs p ∧ ∀ d, d ∣ natAbs p → d = 1 ∨ d = natAbs p) →
    /// p ∣ a*b → p ∣ a ∨ p ∣ b` — Elements VII.30, transported from
    /// `Nat.euclid_lemma` via `gauss_lemma`. Primality is stated on `natAbs p`,
    /// mirroring `Nat`'s own inline convention (no `Prime` name exists over
    /// either carrier).
    pub euclid_lemma: NameId,
    /// `euclid_infinitude : ∀ n, ∃ p, n < p ∧
    /// (2 ≤ natAbs p ∧ ∀ x, x ∣ natAbs p → x = 1 ∨ x = natAbs p)` — Euclid's
    /// theorem (infinitude of primes), transported from `Nat.exists_prime_gt`.
    /// No `Prime` name is introduced on either carrier — primality stays
    /// inline, mirroring `euclid_lemma`'s own convention (`gcd.rs`'s doc
    /// comment on `declare_euclid_infinitude` has the full reasoning).
    pub euclid_infinitude: NameId,

    /// `prime_dvd_mul' : ∀ (m n : Int) (p : Nat), (2 ≤ p ∧ ∀ d, d ∣ p → d = 1
    /// ∨ d = p) → ofNat p ∣ m*n → ofNat p ∣ m ∨ ofNat p ∣ n` — `ml430` mirror
    /// `Int.Prime.dvd_mul'` (`F:ml430-int-prime-dvd-mul-23b73e69`). Direct
    /// application of [`Self::euclid_lemma`] at `pr := ofNat p`: `natAbs
    /// (ofNat p) ≡ p` by `rfl`, so the stated primality hypothesis is
    /// definitionally the one `euclid_lemma` needs. See `int_prelude::
    /// prime_dvd_mul_mirrors`.
    pub prime_dvd_mul_prime: NameId,
    /// `prime_dvd_mul : ∀ (m n : Int) (p : Nat), (2 ≤ p ∧ ∀ d, d ∣ p → d = 1
    /// ∨ d = p) → ofNat p ∣ m*n → p ∣ natAbs m ∨ p ∣ natAbs n` — `ml430`
    /// mirror `Int.Prime.dvd_mul` (`F:ml430-int-prime-dvd-mul-90351ba0`).
    /// Same route as [`Self::prime_dvd_mul_prime`], with each disjunct
    /// dropped to `Nat` via [`Self::nat_abs_dvd_nat_abs_of_dvd`]. See
    /// `int_prelude::prime_dvd_mul_mirrors`.
    pub prime_dvd_mul: NameId,
    /// `not_prime_of_int_mul : ∀ (a b : Int) (c : Nat), natAbs a ≠ 1 →
    /// natAbs b ≠ 1 → a*b = ofNat c → ¬(2 ≤ c ∧ ∀ d, d ∣ c → d = 1 ∨ d = c)`
    /// — `ml430` mirror `Int.not_prime_of_int_mul`
    /// (`F:ml430-int-not-prime-of-int-mul-e3060f5d`). Built at `Nat` from
    /// `natAbs a`/`natAbs b`: neither magnitude is `1`, so their product is
    /// composite (a divisor `x := natAbs a` divides the product and, since
    /// `natAbs b ≠ 1`, is not equal to it — `Nat.mul_left_cancel_of_pos`
    /// closes that inequality — nor equal to `1`), and the `x = 0` corner
    /// falls out of `Nat.prime_ne_zero` directly. See
    /// `int_prelude::prime_dvd_mul_mirrors`.
    pub not_prime_of_int_mul: NameId,
    /// `gcd_ne_one_iff_gcd_mul_right_ne_one : ∀ (a : Int) (m n : Nat), Iff
    /// (Not (Eq (gcd a (ofNat m * ofNat n)) one)) (Or (Not (Eq (gcd a (ofNat
    /// m)) one)) (Not (Eq (gcd a (ofNat n)) one)))` — `ml430` mirror
    /// `Int.gcd_ne_one_iff_gcd_mul_right_ne_one`
    /// (`F:ml430-int-gcd-ne-one-iff-gcd-mul-right-ne-one-ae6099bd`). Built at
    /// `Nat` from `x := natAbs a` (`Int.gcd a b` reduces to `Nat.gcd (natAbs
    /// a) (natAbs b)` by `rfl`, and `natAbs (ofNat m * ofNat n)` reduces to
    /// `mul m n`): the already-proved `Nat.coprime_mul_iff` gives `Iff (Eq
    /// (gcd x (m*n)) one) (And (Eq (gcd x m) one) (Eq (gcd x n) one))`, then
    /// two purely-intuitionistic `Iff` transports (`Not`/`Not`, no
    /// decidability) and one classical step — deciding `Eq (gcd x m) one`
    /// via `Nat.beq`'s soundness/completeness — turn `Not (And q1 q2)` into
    /// `Or (Not q1) (Not q2)`. See `int_prelude::prime_dvd_mul_mirrors`.
    pub gcd_ne_one_iff_gcd_mul_right_ne_one: NameId,
    /// `succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul : ∀ (p : Nat), (2 ≤ p ∧ ∀ d,
    /// d ∣ p → d = 1 ∨ d = p) → ∀ (m n : Int) (k l : Nat), ofNat (pow p k) ∣
    /// m → ofNat (pow p l) ∣ n → ofNat (pow p (k+l+1)) ∣ m*n → ofNat (pow p
    /// (k+1)) ∣ m ∨ ofNat (pow p (l+1)) ∣ n` — `ml430` mirror
    /// `Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul`
    /// (`F:ml430-int-succ-dvd-or-succ-dvd-of-succ-sum-dvd-mul-435a4948`).
    /// Bridged to a `Nat`-level core (`X := natAbs m`, `Y := natAbs n`) via
    /// `nat_abs_dvd_nat_abs_of_dvd`/`dvd_of_nat_abs_dvd`/`nat_abs_mul`: write
    /// `X = p^k·x'`, `Y = p^l·y'` (`Nat.dvd` elimination), regroup `X·Y =
    /// p^(k+l)·(x'·y')` (`Nat.pow_add`, `Nat.mul_assoc`/`mul_comm`), cancel
    /// the positive factor `p^(k+l)` from `p^(k+l+1) ∣ X·Y` (`Nat.pow_pos`,
    /// `Nat.mul_left_cancel_of_pos`) to get `p ∣ x'·y'`, then
    /// `Nat.euclid_lemma` gives `p ∣ x'` or `p ∣ y'`, each of which regroups
    /// back to `p^(k+1) ∣ X` or `p^(l+1) ∣ Y`. See
    /// `int_prelude::prime_dvd_mul_mirrors`.
    pub succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul: NameId,

    // --- the Chinese Remainder Theorem ----------------------------------------
    /// `crt_exists : ∀ m n a b, 0 < m → 0 < n → Coprime m n →
    /// ∃ x, ModEq m x a ∧ ModEq n x b`.
    pub crt_exists: NameId,
    /// `crt_unique : ∀ m n x y, 0 < m → 0 < n → Coprime m n →
    /// ModEq m x y → ModEq n x y → ModEq (m*n) x y`.
    ///
    /// The `0 < m*n` hypothesis this once carried is GONE: `Int.mul_pos` now
    /// derives it internally from `0 < m` and `0 < n`. Strictly fewer
    /// hypotheses, same conclusion.
    pub crt_unique: NameId,

    // --- the rationals, as a normalised structure -----------------------------
    /// `Rat : Type` — a normalised `num/den` pair carrying its own positivity
    /// and reducedness proofs. Not a quotient: this kernel has no `Quot.sound`.
    pub rat: NameId,
    /// `Rat.mk : (num : Int) → (den : Nat) → 1 ≤ den → gcd (natAbs num) den = 1 → Rat`.
    pub rat_mk: NameId,
    /// `Rat.normalize : (num : Int) → (den : Nat) → 1 ≤ den → Rat` — the smart
    /// constructor, dividing through by `gcd (natAbs num) den`.
    pub rat_normalize: NameId,
    /// `Rat.num : Rat → Int` — the numerator projection.
    /// `Rat.rec` — the kernel-generated recursor for the single-constructor
    /// structure, which is both the projection mechanism and the way to reach
    /// its proof fields.
    pub rat_rec: NameId,
    /// `Rat.num : Rat → Int` — the numerator projection.
    pub rat_num: NameId,
    /// `Rat.den : Rat → Nat` — the denominator projection.
    pub rat_den: NameId,
    /// `Rat.den_pos : ∀ q, 1 ≤ Rat.den q` — the positivity field, projected.
    pub rat_den_pos: NameId,
    /// `Rat.mul : Rat → Rat → Rat` — multiplication, renormalising the product.
    pub rat_mul: NameId,
    /// `Rat.reduced : ∀ q, gcd (natAbs (Rat.num q)) (Rat.den q) = 1` — the
    /// reducedness field, projected.
    pub rat_reduced: NameId,
    /// `Rat.neg : Rat → Rat` — negation, which preserves reducedness.
    pub rat_neg: NameId,
    /// `Rat.add : Rat → Rat → Rat` — addition over a common denominator.
    pub rat_add: NameId,
    /// `eq_em : ∀ (a b : Int), Or (Eq Int a b) (Not (Eq Int a b))`.
    pub eq_em: NameId,

    // --- `Int.IsCommRing` (`rings` curriculum node, `int_prelude::ring`) -----
    /// `IsCommRing (add mul : Int → Int → Int) (neg : Int → Int) (zero one :
    /// Int) : Prop := add_comm ∧ (add_assoc ∧ (add_zero ∧ (add_neg ∧ (mul_comm
    /// ∧ (mul_assoc ∧ (mul_one ∧ distrib))))))` — `Rat.IsField`'s own first
    /// eight leaves, over `Int`, minus the two that make a ring a field.
    pub is_comm_ring: NameId,
    /// `int_isCommRing : IsCommRing Int.add Int.mul Int.neg Int.zero Int.one`
    /// — the worked instance.
    pub int_is_comm_ring: NameId,
    /// `mul_eq_zero : ∀ a b, mul a b = zero → a = zero ∨ b = zero` — ℤ is an
    /// integral domain, the consequence a general commutative ring does not
    /// have (`Int.IsCommRing`'s own doc comment: ℤ/6 does not).
    pub mul_eq_zero: NameId,

    // --- `Int.factorial`, and the self-inverse step toward Wilson's theorem --
    /// `Int.factorial : Nat → Int := Int.prodRange (fun k => Int.ofNat (Nat.succ k))`
    /// — `factorial n = 1 * 2 * … * n`, mirroring `Nat.factorial`'s own
    /// right-multiplying convention.
    pub factorial: NameId,
    /// `factorial_zero : Eq Int (factorial zero) one` — closes by `Eq.refl`.
    pub factorial_zero: NameId,
    /// `factorial_succ : ∀ n, Eq Int (factorial (succ n)) (mul (factorial n) (ofNat (succ n)))`
    /// — closes by `Eq.refl`.
    pub factorial_succ: NameId,
    /// `self_inverse_mod_prime :
    /// ∀ p a, (2 ≤ natAbs p ∧ ∀ d, d ∣ natAbs p → d = 1 ∨ d = natAbs p) →
    ///   0 < p → 1 ≤ a → a ≤ p-1 → ModEq p (a*a) one →
    ///   Or (ModEq p a one) (ModEq p a (p-one))` — an element that is its own
    /// modular inverse is congruent to `1` or `-1`, via `Int.euclid_lemma`
    /// deciding which factor of `(a-1)(a+1)` `p` divides.
    pub self_inverse_mod_prime: NameId,
    /// `factorial_pos : ∀ n, 0 < factorial n`.
    pub factorial_pos: NameId,
    /// `of_nat_pow : ∀ (a n : Nat), Eq Int (ofNat (pow a n)) (pow (ofNat a) n)` —
    /// `Int.ofNat` is a ring homomorphism on `pow` at a **symbolic** exponent,
    /// which is genuinely a proof (induction on `n`), not a `refl`: the
    /// `ofNat`-branch reduction that makes `Int.add`/`Int.mul` transparent on
    /// concrete constructors does not reach through `Nat.rec`'s own scrutinee
    /// when the exponent is a free variable.
    pub of_nat_pow: NameId,
    /// `pow_prime_sub_one_modeq_one :
    /// ∀ p a, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → 0 < a → a < p →
    ///   ModEq (ofNat p) (pow (ofNat a) (p-1)) one` —
    /// the coprime form of Fermat's little theorem: `p ∤ a ⟹ a^(p−1) ≡ 1 [p]`.
    /// Route: `Nat.pow_prime_modeq_self` gives `a^p ≡ a [p]` over `ℕ`;
    /// `Nat.pow_succ` (transported along `Nat.sub_add_cancel`'s `succ(p-1)=p`)
    /// splits `a^p` into `a^(p-1)*a`; `Int.modEq_of_nat_modEq` casts the whole
    /// congruence to `ℤ`; `of_nat_pow` reshapes the `ℕ`-side power into
    /// `Int.pow`; and `Int.modEq_cancel`, fed `Nat.coprime_of_lt_prime`,
    /// cancels the surviving factor of `a`.
    pub pow_prime_sub_one_modeq_one: NameId,
    /// `mul_inv_of_pow :
    /// ∀ p a, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → 0 < a → a < p →
    ///   ModEq (ofNat p) (mul (ofNat a) (pow (ofNat a) (p-2))) one` — one more
    /// split of [`Self::pow_prime_sub_one_modeq_one`]: `a * a^(p-2) ≡ 1 [p]`,
    /// the executable-inverse form Fermat's coprime congruence unlocks.
    pub mul_inv_of_pow: NameId,
    /// `Nat.inverseIndex : Nat → Nat → Nat :=
    /// fun p k => natAbs (emod (pow (ofNat (succ k)) (p-2)) (ofNat p)) - 1` —
    /// the closed-form `Nat → Nat` modular-inverse index map
    /// `Int.prodRange_permute` needs a concrete `σ` from. Declared under the
    /// `Nat` namespace (not `Int`), even though its body computes through
    /// `Int.pow`/`Int.emod`/`Int.natAbs`, because its type is `Nat → Nat → Nat`
    /// — see `wilson.rs`'s doc comment on `declare_inverse_index`.
    pub inverse_index: NameId,
    /// `Nat.inverseIndex_maps_into :
    /// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
    ///   MapsInto (fun k => inverseIndex p k) (p-1)` — the inverse of a
    /// residue is a residue: `Int.emod` always lands in `[0, ofNat p)`, and
    /// that bound transports to `ℕ` for free (`Int.lt` on two
    /// `ofNat`-headed arguments reduces structurally to `Nat.lt`).
    pub inverse_index_maps_into: NameId,
    /// `Nat.inverseIndex_injective :
    /// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
    ///   InjectiveOn (fun k => inverseIndex p k) (p-1)` — two indices with
    /// the same inverse are the same index, via `Int.modEq_inverse_unique`.
    pub inverse_index_injective: NameId,
    /// `Nat.inverseIndex_fixed_point :
    /// ∀ p k, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → Lt k (p-1) →
    ///   Eq Nat (inverseIndex p k) k → Or (Eq Nat k zero) (Eq Nat k (p-2))` —
    /// the converse of the two direct computations `σ 0 = 0` / `σ (p-2) =
    /// p-2`: the only residues that are their own modular inverse are `1`
    /// and `p-1`, i.e. the only fixed indices of `σ := Nat.inverseIndex p`
    /// are `0` and `p-2`. Built from [`Self::self_inverse_mod_prime`] (the
    /// mathematical content) transported across the index/residue
    /// correspondence `a := ofNat(k+1)`.
    pub inverse_index_fixed_point: NameId,
    /// `Nat.inverseIndex_involutive :
    /// ∀ p k, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) → Lt k (p-1) →
    ///   Eq Nat (inverseIndex p (inverseIndex p k)) k` — `σ := Nat.inverseIndex
    /// p` is its own inverse: applying it twice returns the original index,
    /// for every `k`, fixed points included. Built the same way as
    /// [`Self::inverse_index_fixed_point`]: [`Self::mul_inv_of_pow`] applied
    /// at both `k`'s own residue and its image, glued by
    /// [`Self::mod_eq_inverse_unique`] (both residues are inverses of the
    /// *same* value, hence congruent to each other, hence — being canonical
    /// representatives in `[0,p)` — literally equal).
    pub inverse_index_involutive: NameId,
    /// `Nat.inverseIndex_fixes_zero :
    /// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
    ///   Eq Nat (inverseIndex p zero) zero` — the direct computation `σ 0 =
    /// 0` (`σ := Nat.inverseIndex p`): `1` is its own modular inverse.
    pub inverse_index_fixes_zero: NameId,
    /// `Nat.inverseIndex_fixes_last :
    /// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
    ///   Eq Nat (inverseIndex p (p-2)) (p-2)` — the other direct computation
    /// `σ (p-2) = p-2`: `p-1 ≡ -1 [p]` is its own modular inverse.
    pub inverse_index_fixes_last: NameId,
    /// `Nat.inverseIndex_interior_fixed_point_free :
    /// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
    ///   ∀ k, Lt zero k → Lt k (p-2) → Not (Eq Nat (inverseIndex p k) k)` —
    /// the immediate contrapositive of [`Self::inverse_index_fixed_point`]:
    /// on the interior `{1,…,p-3}` (excluding both of `σ`'s exactly two
    /// fixed points), `σ` is fixed-point-free.
    pub inverse_index_interior_fixed_point_free: NameId,
    /// `factorial_sq_modeq_one :
    /// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
    ///   ModEq (ofNat p) (mul (factorial (p-1)) (factorial (p-1))) one` —
    /// **the collapse lemma**: `((p-1)!)^2 ≡ 1 [p]`, for every prime `p`.
    /// Built from `Int.prodRange_permute` at `σ := Nat.inverseIndex p`, the
    /// new `Int.prodRange_mul`/`Int.modEq_prodRange_lt` (`prod.rs`), and
    /// `Int.mul_inv_of_pow`; see `wilson.rs`'s doc section right above
    /// `declare_factorial_sq_modeq_one` for exactly what this does and does
    /// NOT establish (the sign is not decided, so `Int.wilson` does not
    /// follow from this alone).
    pub factorial_sq_modeq_one: NameId,
    /// `prod_range_pairing_collapse :
    /// ∀ bigp, Lt zero bigp → ∀ n F σ,
    ///   InjectiveOn σ n → MapsInto σ n →
    ///   (∀ k, Lt k n → Not (Eq Nat (σ k) k)) →
    ///   (∀ k, Lt k n → Eq Nat (σ (σ k)) k) →
    ///   (∀ k, Lt k n → ModEq bigp (mul (F k) (F (σ k))) one) →
    ///   ModEq bigp (prodRange F n) one` —
    /// **the interior collapse**: a fixed-point-free involution pairing up
    /// `[0,n)`, with every pair's product `≡ 1`, collapses the whole
    /// `prodRange` to `1`. Proved by a two-step induction (`And (family n)
    /// (family (succ n))` by ordinary `Nat.rec`, no `WellFounded.fix`
    /// needed): the step peels the top two indices directly when they are
    /// already paired with each other, or conjugates `σ` by a two-point
    /// swap first (`wilson.rs`'s local `tau_raw`, mirroring
    /// `Nat.transposition`, plus `int_prelude/prod.rs`'s `point_swap` and
    /// `Int.prodRange_swap` for the value side) when they are not. See
    /// `wilson.rs`'s module doc above this declaration for the full route.
    pub prod_range_pairing_collapse: NameId,
    /// `factorial_interior_modeq_one :
    /// ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
    ///   ModEq (ofNat p) (prodRange (fun i => ofNat (succ (succ i))) (p-3)) one` —
    /// the interior of Wilson's product (indices `{2,…,p-2}` reindexed down to
    /// `[0,p-3)`) collapses to `1`, by `prod_range_pairing_collapse` applied to
    /// the reindexed `σ' i := (Nat.inverseIndex p (succ i)) - 1`. Statement is
    /// clean (no side condition beyond primality); the *proof* case-splits
    /// nowhere either — every fact `σ'` needs is derived from a hypothesis
    /// `i < p-3` that is already in hand, so `p = 2`/`p = 3` (where the
    /// interior is empty) fall out vacuously rather than needing separate
    /// handling. See `wilson.rs`'s module doc for the full route and what
    /// still remains (`Int.wilson` itself).
    pub factorial_interior_modeq_one: NameId,
    /// `wilson : ∀ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) →
    ///   ModEq (ofNat p) (factorial (p-1)) (neg one)` — **Wilson's theorem**:
    /// `p` prime ⟹ `(p-1)! ≡ -1 [p]`. `factorial (p-1) = mul (prodRange F
    /// (p-2)) (F (p-2))`, and `F (p-2) = ofNat(p-1) ≡ -1 [p]` unconditionally;
    /// `prodRange F (p-2) ≡ 1 [p]` case-splits on `p ≥ 3` (via
    /// `prodRange_shiftFront` and `factorial_interior_modeq_one`) vs `p = 2`
    /// (`p-2 = 0` directly, so the interior is empty and `prodRange_zero`
    /// closes it) — the ONE place in the whole assembly `p = 2` needs its own
    /// argument. See `wilson.rs`'s module doc above `declare_wilson` for the
    /// full route.
    pub wilson: NameId,
    /// `dvd_factorial_of_le : ∀ (dd n : Nat), Le 1 dd → Le dd n →
    ///   dvd (ofNat dd) (factorial n)` — a positive `dd ≤ n` divides `n!`,
    /// transported to `ℤ`. Proved by direct induction over `Int.factorial`
    /// (mirrors `Nat.dvd_factorial_of_le`'s own induction; not derived FROM
    /// it, since `Int.factorial n` and `ofNat (Nat.factorial n)` are not
    /// definitionally equal). The workhorse [`Self::wilson_converse`] needs.
    pub dvd_factorial_of_le: NameId,
    /// `wilson_converse : ∀ n, Le 2 n →
    ///   ModEq (ofNat n) (factorial (n-1)) (neg one) →
    ///   (2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n)` — **the converse of Wilson's
    /// theorem**: `(n-1)! ≡ -1 [n]` (with `n ≥ 2`) forces `n` prime. Proved
    /// fully constructively (no `Classical.em`) in the conjunctive `Prime n`
    /// form directly, not a contrapositive: for an arbitrary divisor `d` of
    /// `n`, `Nat.lt_or_eq_of_le` splits `d ≤ n` into `d < n` or `d = n`; the
    /// `d = n` branch is immediate, and the `d < n` branch derives `d = 1`
    /// from `d ∣ (n-1)!` ([`Self::dvd_factorial_of_le`]) and
    /// `n ∣ (-1 - (n-1)!)` ([`Self::mod_eq_iff_dvd`]'s `mp` applied to the
    /// hypothesis): `Int.dvd_add` combines the two into `d ∣ -1`, and
    /// `Nat.eq_one_of_dvd_one` closes it. See `wilson.rs`'s
    /// `declare_wilson_converse` for the full route.
    pub wilson_converse: NameId,
    /// `wilson_iff : ∀ n, Le 2 n →
    ///   ((2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n) ↔
    ///     ModEq (ofNat n) (factorial (n-1)) (neg one))` — Wilson's theorem
    /// AND its converse combined: for `n ≥ 2`, primality is EQUIVALENT to
    /// `(n-1)! ≡ -1 [n]`, a genuine decision criterion for primality, not
    /// merely a necessary condition. `Iff.intro` of [`Self::wilson`] (mp)
    /// and [`Self::wilson_converse`] (mpr).
    pub wilson_iff: NameId,

    // --- quadratic residues, and Euler's criterion's unconditional half ----
    /// `IsQuadraticResidue : Int → Int → Prop :=
    /// fun p a => ∃ x, ModEq p (x*x) a` — `a` is a quadratic residue mod `p`.
    pub is_quadratic_residue: NameId,
    /// `is_quadratic_residue_one : ∀ p, IsQuadraticResidue p one` —
    /// `1` is always a residue, witness `x := one`.
    pub is_quadratic_residue_one: NameId,
    /// `is_quadratic_residue_mul :
    /// ∀ p a b, 0 < p → IsQuadraticResidue p a → IsQuadraticResidue p b →
    ///   IsQuadraticResidue p (mul a b)` — residues are closed under
    /// multiplication, witness `x*y` from `a`'s and `b`'s own witnesses.
    pub is_quadratic_residue_mul: NameId,
    /// `euler_criterion_pm_one :
    /// ∀ pp aa m, (2 ≤ pp ∧ ∀ d, d ∣ pp → d = 1 ∨ d = pp) →
    ///   Eq Nat (pp-1) (m+m) → 0 < aa → aa < pp →
    ///   Or (ModEq (ofNat pp) (pow (ofNat aa) m) one)
    ///      (ModEq (ofNat pp) (pow (ofNat aa) m) (neg one))` — Euler's
    /// criterion's unconditional half: `a^((p-1)/2) ≡ ±1 [p]`, with the
    /// half-exponent `m` supplied via the hypothesis `p-1 = m+m` rather than
    /// computed by division (see `euler.rs`'s module doc for why). Does NOT
    /// decide which sign holds, or relate the sign to `IsQuadraticResidue` —
    /// that direction needs a primitive root or a counting argument this
    /// prelude does not build.
    pub euler_criterion_pm_one: NameId,
    /// `euler_criterion_residue_imp_one :
    /// ∀ pp aa m, (2 ≤ pp ∧ ∀ d, d ∣ pp → d = 1 ∨ d = pp) →
    ///   Eq Nat (pp-1) (m+m) → 0 < aa → aa < pp →
    ///   IsQuadraticResidue (ofNat pp) (ofNat aa) →
    ///   ModEq (ofNat pp) (pow (ofNat aa) m) one` — Euler's criterion, the
    /// NECESSARY direction: a quadratic residue's half-power is `≡ 1`, not
    /// merely `≡ ±1`. Route (`qr_criterion.rs`): the witness `x` (`x*x ≡ a`)
    /// is reduced to its canonical residue `r := emod x p` (in range for
    /// Fermat), Fermat gives `r^(p-1) ≡ 1` hence `r^(m+m) ≡ 1`, `ModEq.pow`
    /// transports that along `x ≡ r` to `x^(m+m) ≡ 1`, and
    /// `Int.pow_add`/[`qr_criterion::pow_mul_self`](crate) identify
    /// `x^(m+m)` with `(x*x)^m`, which `ModEq.pow` along `x*x ≡ a` finally
    /// relates to `a^m`. Does NOT prove the converse (`a^m ≡ 1 → residue`),
    /// which still needs a primitive root or a root-counting argument this
    /// prelude does not build — see [`Self::euler_criterion_pm_one`].
    pub euler_criterion_residue_imp_one: NameId,
    /// `euler_criterion_neg_one_imp_not_residue :
    /// ∀ pp aa m, (2 ≤ pp ∧ ∀ d, d ∣ pp → d = 1 ∨ d = pp) → Lt 2 pp →
    ///   Eq Nat (pp-1) (m+m) → 0 < aa → aa < pp →
    ///   ModEq (ofNat pp) (pow (ofNat aa) m) (neg one) →
    ///   Not (IsQuadraticResidue (ofNat pp) (ofNat aa))` — Euler's
    /// criterion's non-residue detector: for an ODD prime `p` (`2 < p`), a
    /// half-power `≡ -1` rules out `a` being a residue. Contrapositive of
    /// [`Self::euler_criterion_residue_imp_one`]: if `a` were a residue its
    /// half-power would be `≡ 1`, so combined with the `≡ -1` hypothesis
    /// `1 ≡ -1 [p]`, i.e. `p ∣ 2`; `Nat.le_of_dvd` then forces `p ≤ 2`,
    /// contradicting `2 < p`.
    pub euler_criterion_neg_one_imp_not_residue: NameId,

    // --- the Euler's-totient-theorem unit-permutation step (`euler_totient.rs`) ---
    /// `euler_unit_coprime : ∀ n a k, 0 < n → Coprime a n → Coprime k n →
    /// Coprime (emod (mul a k) n) n` — multiplication by a unit `a` maps the
    /// coprime-residue subset of `[0,n)` into itself (`MapsInto`, one half of
    /// Euler's totient theorem's permutation step). Does NOT by itself give
    /// bijectivity of that map on the subset — see `euler_totient.rs`'s
    /// module doc for exactly what is still missing (a predicate-scoped
    /// pigeonhole, not built here or anywhere in this kernel yet).
    pub euler_unit_coprime: NameId,
    /// `euler_unit_injective : ∀ n a i j, 0 < n → Coprime a n → 0 ≤ i →
    /// i < n → 0 ≤ j → j < n → Eq Int (emod (mul a i) n) (emod (mul a j) n) →
    /// Eq Int i j` — multiplication by a unit `a` is injective on the WHOLE
    /// `[0,n)` (of which injectivity on the coprime-residue subset is a free
    /// corollary, restricting `i,j` to that subset).
    pub euler_unit_injective: NameId,
    /// `fib_cassini : ∀ n, Eq Int (sub (mul (ofNat (Nat.fib (n+2))) (ofNat
    /// (Nat.fib n))) (mul (ofNat (Nat.fib (n+1))) (ofNat (Nat.fib (n+1)))))
    /// (pow (neg one) (succ n))` — Cassini's identity, shifted so every index
    /// is a literal successor and `(-1)^n` is `Int.pow` at a negative base
    /// (no parity case-split) rather than a computed exponent. See
    /// `fibonacci.rs`'s module doc for the hand check and the proof's algebra.
    pub fib_cassini: NameId,
    /// `fib : Int → Int` — the sign-extended Fibonacci sequence: `fib (ofNat
    /// n) := ofNat (Nat.fib n)`, `fib (negSucc m) := pow (neg one) m * ofNat
    /// (Nat.fib (succ m))` (the standard extension `fib(-n) = (-1)^(n+1)
    /// fib(n)`, shifted to use the natural exponent `m` directly). One
    /// `Int.rec` case split, no new recursion device — see `fibonacci.rs`'s
    /// module doc for the hand check.
    pub fib: NameId,
    /// `fib_two_mul_add_one_pos : ∀ n, Lt zero (fib (2*n+1))` — the Fibonacci
    /// sequence is strictly positive at every ODD index, in either direction
    /// of `ℤ`. See `fibonacci.rs`'s module doc for the proof.
    pub fib_two_mul_add_one_pos: NameId,
    /// `Even : Int → Prop := fun n => Nat.Even (natAbs n)` — magnitude alone
    /// decides parity, since negation does not change it. See `parity.rs`'s
    /// module doc for why this form was chosen over a fresh `Int`-level
    /// existential.
    pub even: NameId,
    /// `Odd : Int → Prop := fun n => Nat.Odd (natAbs n)`. See `parity.rs`.
    pub odd: NameId,
    /// `odd_iff_nat_abs_odd : ∀ n, Iff (Odd n) (Nat.Odd (natAbs n))` — named,
    /// discoverable API surface for what [`Self::odd`]'s definition already
    /// gives for free.
    pub odd_iff_nat_abs_odd: NameId,
    /// `even_iff_nat_abs_even : ∀ n, Iff (Even n) (Nat.Even (natAbs n))` —
    /// [`Self::odd_iff_nat_abs_odd`] with `Even`/`Odd` swapped.
    pub even_iff_nat_abs_even: NameId,
    /// `emod_two_eq_zero_or_one : ∀ n, Or (Eq (emod n 2) 0) (Eq (emod n 2)
    /// 1)` — the sign-general low-bit split, proved by `Int.rec` on `n` plus
    /// `Nat.mod_two_eq_zero_or_one` on the bound `Nat` field of each branch
    /// (not a public `ml430` mirror itself; the load-bearing step under
    /// [`Self::emod_two_ne_zero`]/[`Self::emod_two_ne_one`]). See
    /// `parity.rs`'s module doc.
    pub emod_two_eq_zero_or_one: NameId,
    /// `emod_two_ne_zero : ∀ n, Iff (Not (Eq (emod n 2) 0)) (Eq (emod n 2)
    /// 1)`.
    pub emod_two_ne_zero: NameId,
    /// `emod_two_ne_one : ∀ n, Iff (Not (Eq (emod n 2) 1)) (Eq (emod n 2)
    /// 0)`.
    pub emod_two_ne_one: NameId,
    /// `ediv_two_mul_two_of_even : ∀ n, Even n → Eq (mul (ediv n 2) 2) n`.
    pub ediv_two_mul_two_of_even: NameId,
    /// `ediv_two_mul_two_add_one_of_odd : ∀ n, Odd n → Eq (add (mul (ediv n
    /// 2) 2) one) n`.
    pub ediv_two_mul_two_add_one_of_odd: NameId,
    /// `add_one_ediv_two_mul_two_of_odd : ∀ n, Odd n → Eq (add one (mul
    /// (ediv n 2) 2)) n`.
    pub add_one_ediv_two_mul_two_of_odd: NameId,
    /// `odd_of_mul_left : ∀ m n, Odd (mul m n) → Odd m`.
    pub odd_of_mul_left: NameId,
    /// `odd_of_mul_right : ∀ m n, Odd (mul m n) → Odd n`.
    pub odd_of_mul_right: NameId,
    /// `even_add : ∀ m n, Iff (Even (add m n)) (Iff (Even m) (Even n))` —
    /// `F:ml430-int-even-add-3c4536e3`. See `parity.rs`'s `emod` additive
    /// law (`modeq_add`).
    pub even_add: NameId,
    /// `even_add' : ∀ m n, Iff (Even (add m n)) (Iff (Odd m) (Odd n))` —
    /// `F:ml430-int-even-add-bc8e1394`, a DIFFERENT proposition from
    /// [`Self::even_add`] despite sharing the Mathlib base name (confirmed
    /// against Mathlib's `Int.even_add`/`Int.even_add'` directly).
    pub even_add_prime: NameId,
    /// `even_add_one : ∀ n, Iff (Even (add n 1)) (Not (Even n))` —
    /// `F:ml430-int-even-add-one-af33da18`.
    pub even_add_one: NameId,
    /// `fib_of_odd : ∀ n, Odd n → Eq Int (fib n) (ofNat (Nat.fib (natAbs
    /// n)))` — at an odd index the sign-extended `fib` agrees with the plain
    /// `Nat`-valued Fibonacci sequence at the magnitude, in EITHER direction
    /// of `ℤ`. See `fibonacci.rs`'s module doc for the proof (cheap once
    /// `Odd`/`Even` are stated via `natAbs`, per the earlier lane's
    /// prediction).
    pub fib_of_odd: NameId,
    /// `induction_on : ∀ (P : Int → Prop), P zero → (∀ n, P n → P (add n
    /// one)) → (∀ n, P n → P (sub n one)) → ∀ n, P n` — two-sided induction
    /// over `ℤ`: prove the motive at `0` and step in both directions.
    ///
    /// `Int.rec` is a *case split* into `ofNat`/`negSucc`, not an induction
    /// principle; this is the first combinator in the development that
    /// actually inducts over `ℤ`. See `two_sided_induction.rs`'s module doc
    /// for why every bridging step is pure reduction.
    pub induction_on: NameId,
    /// `fib_rec : ∀ n, Eq Int (fib (add n (ofNat 2))) (add (fib (add n one))
    /// (fib n))` — the Fibonacci recurrence at **every** integer index, the
    /// negative ones included. `Nat.fib_add_two` is the `ℕ` half and says
    /// nothing below `0`; `Int.fib`'s `negSucc` clause is a definition, not a
    /// recurrence. Three cases (`n ≥ 0`, `n ∈ {-1,-2}`, `n ≤ -3`) — see
    /// `fibonacci.rs`'s `declare_fib_rec` doc.
    pub fib_rec: NameId,
    /// `fib_add : ∀ m n, Eq Int (fib (add m n)) (add (mul (fib (sub m one))
    /// (fib n)) (mul (fib m) (fib (add n one))))` — Mathlib's `Int.fib_add`,
    /// over the constructed `ℤ`. Proved by `Int.induction_on` on `n` with the
    /// paired motive `P k ∧ P (k+1)`; it does **not** reduce to `Nat.fib_add`,
    /// since even the `m = 0` corner reads a value at a negative index. See
    /// `fibonacci.rs`'s `declare_fib_add` doc.
    pub fib_add: NameId,
    /// `fib_two_mul : ∀ n, Eq Int (fib (mul two n)) (mul (fib n)
    /// (sub (mul two (fib (add n one))) (fib n)))` — Mathlib's
    /// `Int.fib_two_mul`. Direct algebra from `fib_add n n` and `fib_rec`,
    /// no induction; see `fibonacci.rs`'s `declare_fib_two_mul` doc.
    pub fib_two_mul: NameId,
    /// `fib_two_mul_add_two : ∀ n, Eq Int (fib (add (mul two n) two))
    /// (mul (fib (add n one)) (add (mul two (fib n)) (fib (add n one))))` —
    /// Mathlib's `Int.fib_two_mul_add_two`. Same shape of proof as
    /// `fib_two_mul`, one index up (`fib_add (n+1) (n+1)` plus `fib_rec`);
    /// see `fibonacci.rs`'s `declare_fib_two_mul_add_two` doc.
    pub fib_two_mul_add_two: NameId,

    // -- `int-dvd-mirrors` lane: `ml430` divisibility/gcd/`ModEq` mirrors
    // `gcd.rs`/`dvd.rs`/`modeq.rs`/`modeq_family.rs` did not already close
    // (`int_prelude/dvd_gcd_mirrors.rs`). Appended here, not interleaved with
    // the existing fields above, to keep this a pure-addition diff in a
    // struct many lanes touch.
    /// `dvd_gcd_nat : ∀ (a b : Int) (c : Nat), ofNat c ∣ a → ofNat c ∣ b →
    /// c ∣ gcd a b` -- Mathlib's `Int.dvd_gcd` (the `Nat`-typed-divisor form;
    /// [`Self::dvd_gcd`] above is the *coe* form, Mathlib's
    /// `Int.dvd_coe_gcd`).
    pub dvd_gcd_nat: NameId,
    /// `dvd_gcd_nat_iff : ∀ (a b : Int) (c : Nat),
    /// Iff (c ∣ gcd a b) (And (ofNat c ∣ a) (ofNat c ∣ b))` -- Mathlib's
    /// `Int.dvd_gcd_iff`.
    pub dvd_gcd_nat_iff: NameId,
    /// `dvd_coe_gcd_iff : ∀ (a b c : Int),
    /// Iff (c ∣ ofNat (gcd a b)) (And (c ∣ a) (c ∣ b))` -- Mathlib's
    /// `Int.dvd_coe_gcd_iff`.
    pub dvd_coe_gcd_iff: NameId,
    /// `gcd_dvd_iff : ∀ (a b : Int) (n : Nat), Iff (Nat.dvd (gcd a b) n)
    /// (Exists (fun x => Exists (fun y => Eq Int (ofNat n) (a*x+b*y))))` --
    /// Mathlib v4.30's `Int.gcd_dvd_iff`. Closes
    /// `F:ml430-int-gcd-dvd-iff-66fa03b3`. See `int_prelude::gcd_dvd_iff`.
    pub gcd_dvd_iff: NameId,
    /// `exists_gcd_one : ∀ m n, Lt zero (gcd m n) → Exists (fun m' => Exists
    /// (fun n' => And (Eq Nat (gcd m' n') 1) (And (Eq Int m (m'*ofNat (gcd m
    /// n))) (Eq Int n (n'*ofNat (gcd m n))))))` -- Mathlib v4.30's
    /// `Int.exists_gcd_one`. Closes `F:ml430-int-exists-gcd-one-d8820780`.
    /// See `int_prelude::exists_gcd_one`.
    pub exists_gcd_one: NameId,
    /// `exists_gcd_one' : ∀ m n, Lt zero (gcd m n) → Exists (fun g => And
    /// (Lt zero g) (Exists (fun m' => Exists (fun n' => And (Eq Nat (gcd m'
    /// n') 1) (And (Eq Int m (m'*ofNat g)) (Eq Int n (n'*ofNat g)))))))` --
    /// Mathlib v4.30's `Int.exists_gcd_one'`. Closes
    /// `F:ml430-int-exists-gcd-one-657db3e2`. See
    /// `int_prelude::exists_gcd_one`.
    pub exists_gcd_one_prime: NameId,
    /// `ediv_gcd_ne_zero_of_ne_zero_left : ∀ a b, a ≠ 0 →
    /// a.ediv (ofNat (gcd a b)) ≠ 0` -- Mathlib's
    /// `Int.ediv_gcd_ne_zero_of_ne_zero_left`.
    pub ediv_gcd_ne_zero_of_ne_zero_left: NameId,
    /// `ediv_gcd_ne_zero_if_ne_zero_right : ∀ a b, b ≠ 0 →
    /// b.ediv (ofNat (gcd a b)) ≠ 0` -- Mathlib's
    /// `Int.ediv_gcd_ne_zero_if_ne_zero_right`.
    pub ediv_gcd_ne_zero_if_ne_zero_right: NameId,
    /// `mod_eq_add : ∀ n a b c e, ModEq n a b → ModEq n c e →
    /// ModEq n (a+c) (b+e)` -- Mathlib's `Int.ModEq.add`, UNCONDITIONAL in
    /// `n`.
    pub mod_eq_add: NameId,
    /// `mod_eq_add_right_cancel : ∀ n a b c, ModEq n (a+c) (b+c) →
    /// ModEq n a b` -- Mathlib's `Int.ModEq.add_right_cancel'` (the
    /// single-`c` cancellation), UNCONDITIONAL in `n`. Not to be confused
    /// with [`Self::mod_eq_add_right_cancel_general`], the 4-variable form.
    pub mod_eq_add_right_cancel: NameId,
    /// `mod_eq_add_left_cancel_general : ∀ n a b c e, ModEq n a b →
    /// ModEq n (a+c) (b+e) → ModEq n c e` -- Mathlib's 4-variable
    /// `Int.ModEq.add_left_cancel`, UNCONDITIONAL in `n`. Not to be confused
    /// with [`Self::mod_eq_add_left_cancel`], the single-`c` form.
    pub mod_eq_add_left_cancel_general: NameId,
    /// `mod_eq_add_right_cancel_general : ∀ n a b c e, ModEq n c e →
    /// ModEq n (a+c) (b+e) → ModEq n a b` -- Mathlib's 4-variable
    /// `Int.ModEq.add_right_cancel`, UNCONDITIONAL in `n`.
    pub mod_eq_add_right_cancel_general: NameId,
    /// `mod_eq_dvd : ∀ n a b, ModEq n a b → n ∣ (b - a)` -- Mathlib's
    /// `Int.ModEq.dvd`, UNCONDITIONAL in `n`.
    pub mod_eq_dvd: NameId,
    /// `mod_eq_emod_eq : ∀ n a b, ModEq n a b → Eq Int (emod a n) (emod b n)`
    /// -- Mathlib's `Int.ModEq.eq`, UNCONDITIONAL in `n`.
    pub mod_eq_emod_eq: NameId,
    /// `mod_eq_mul_general : ∀ n a b c e, ModEq n a b → ModEq n c e →
    /// ModEq n (a*c) (b*e)` -- Mathlib's `Int.ModEq.mul`, UNCONDITIONAL in
    /// `n` (the existing [`Self::mod_eq_mul`] needs `0 < n`).
    pub mod_eq_mul_general: NameId,

    // -- `int-gcd-mul-transport` lane: the ℤ transport of
    // `nat_prelude/gcd_mul_right_mirrors.rs`'s three `ml430` mirrors
    // (`int_prelude/gcd_scaled_mirrors.rs`). Appended here for the same
    // pure-addition-diff reason as the block above.
    /// `dvd_gcd_mul_iff_dvd_mul : ∀ k n m, k ∣ ofNat (gcd k n) * m ↔ k ∣ n * m`
    /// -- Mathlib's `Int.dvd_gcd_mul_iff_dvd_mul`.
    pub dvd_gcd_mul_iff_dvd_mul: NameId,
    /// `dvd_mul_gcd_iff_dvd_mul : ∀ k n m, k ∣ n * ofNat (gcd k m) ↔ k ∣ n * m`
    /// -- Mathlib's `Int.dvd_mul_gcd_iff_dvd_mul`.
    pub dvd_mul_gcd_iff_dvd_mul: NameId,
    /// `dvd_gcd_mul_gcd_iff_dvd_mul : ∀ k n m,
    /// k ∣ (ofNat (gcd k n)) * (ofNat (gcd k m)) ↔ k ∣ n * m` -- Mathlib's
    /// `Int.dvd_gcd_mul_gcd_iff_dvd_mul`.
    pub dvd_gcd_mul_gcd_iff_dvd_mul: NameId,
    /// `mod_eq_cancel_left_div_gcd : ∀ m a b c, 0 < m → ModEq m (c*a) (c*b)
    /// → ModEq (m.ediv (ofNat (m.gcd c))) a b` -- Mathlib's
    /// `Int.ModEq.cancel_left_div_gcd` (`modeq_cancel_div_gcd.rs`).
    pub mod_eq_cancel_left_div_gcd: NameId,
    /// `mod_eq_cancel_right_div_gcd : ∀ m a b c, 0 < m → ModEq m (a*c) (b*c)
    /// → ModEq (m.ediv (ofNat (m.gcd c))) a b` -- Mathlib's
    /// `Int.ModEq.cancel_right_div_gcd` (`modeq_cancel_div_gcd.rs`).
    pub mod_eq_cancel_right_div_gcd: NameId,
    /// `euler_unit_coprime_iff : ∀ n a k, 0 < n → 0 ≤ k → k < n → Coprime a n → (Coprime k n ↔ Coprime (emod (a*k) n) n)`
    /// -- the predicate-preservation step Euler's theorem needs
    /// (`euler_unit_preserve.rs`).
    pub euler_unit_coprime_iff: NameId,
    /// `euler_unit_perm_injective : ∀ n a, 0 < n → Coprime a (ofNat n) →
    /// InjectiveOn (fun k => natAbs (emod (a * ofNat k) (ofNat n))) n` --
    /// the `Nat`-shaped self-map `Int.prodRangeIf_permute` needs, item 1 of
    /// the Fermat -> Euler handoff (`euler_unit_range.rs`).
    pub euler_unit_perm_injective: NameId,
    /// `euler_unit_perm_maps_into : ∀ n a, 0 < n →
    /// MapsInto (fun k => natAbs (emod (a * ofNat k) (ofNat n))) n` --
    /// unconditional in `a`, `euler_unit_range.rs`.
    pub euler_unit_perm_maps_into: NameId,
    /// `prod_range_if_const_eq_pow_count : ∀ pred a n, Eq Int
    /// (prodRange (selector pred (fun _ => a)) n) (pow a (countRange pred n))`
    /// -- item 3(a) of the Fermat -> Euler handoff, a genuinely new
    /// induction pairing `Int.pow` with `Nat.countRange`
    /// (`euler_prod_pow.rs`).
    pub prod_range_if_const_eq_pow_count: NameId,
    /// `prod_range_if_coprime : ∀ pred f n m, 0 < m →
    /// (∀ k, k < n → pred k = true → Coprime (f k) m) →
    /// Coprime (prodRange (selector pred f) n) m` -- a restricted product of
    /// `m`-coprime factors stays coprime to `m`, part of item 3 of the
    /// Fermat -> Euler handoff (`euler_prod_coprime.rs`).
    pub prod_range_if_coprime: NameId,
    /// `prod_range_if_factor_const_left : ∀ pred a f n,
    /// prodRange (selector pred (fun k => a * f k)) n =
    /// (prodRange (selector pred (fun _ => a)) n) * (prodRange (selector pred f) n)`
    /// -- pointwise factoring of a constant out of a restricted product,
    /// part of item 3 of the Fermat -> Euler handoff
    /// (`euler_prod_factor.rs`).
    pub prod_range_if_factor_const_left: NameId,
    /// `prod_range_if_modeq : ∀ n pred f g m, 0 < n →
    /// (∀ k, ModEq n (f k) (g k)) →
    /// ModEq n (prodRange (selector pred f) m) (prodRange (selector pred g) m)`
    /// -- a restricted product reduces mod `n` factor by factor, the
    /// termwise `ModEq` transport step of item 3 of the Fermat -> Euler
    /// handoff (`euler_prod_modeq.rs`).
    pub prod_range_if_modeq: NameId,
    /// `euler_totient_theorem : ∀ n a, 0 < n → Coprime a (ofNat n) →
    /// ModEq (ofNat n) (pow a (totient n)) one` -- Euler's totient theorem
    /// (`euler_assembly.rs`).
    pub euler_totient_theorem: NameId,
}

/// Intern every name the integer development uses. Interning is not
/// declaration: this runs before anything is admitted, so the proof scripts can
/// name a law they have not yet reached.
fn intern_names(kernel: &mut Kernel, nat: NatPrelude) -> IntPrelude {
    let anon = kernel.anon();
    let z = kernel.name_str(anon, "Int");
    let child = |kernel: &mut Kernel, name: &str| kernel.name_str(z, name);
    let nat_root = nat.nat;
    let rat = kernel.name_str(anon, "Rat");
    let le_name = child(kernel, "le");
    let lt_name = child(kernel, "lt");
    let le_elim = kernel.name_str(le_name, "elim");
    let lt_elim = kernel.name_str(lt_name, "elim");
    IntPrelude {
        logic: nat.logic,
        nat,
        z,
        of_nat: child(kernel, "ofNat"),
        neg_succ: child(kernel, "negSucc"),
        rec: child(kernel, "rec"),
        neg_of_nat: child(kernel, "negOfNat"),
        sub_nat_nat: child(kernel, "subNatNat"),
        sub_nat_nat_succ_succ: child(kernel, "subNatNat_succ_succ"),
        sub_nat_nat_add_add: child(kernel, "subNatNat_add_add"),
        sub_nat_nat_add_add_left: child(kernel, "subNatNat_add_add_left"),
        sub_nat_nat_zero: child(kernel, "subNatNat_zero"),
        zero_sub_nat_nat: child(kernel, "zero_subNatNat"),
        sub_nat_nat_add_left: child(kernel, "subNatNat_add_left"),
        sub_nat_nat_add_right: child(kernel, "subNatNat_add_right"),
        sub_nat_nat_elim: child(kernel, "subNatNat_elim"),
        of_nat_add_sub_nat_nat: child(kernel, "ofNat_add_subNatNat"),
        sub_nat_nat_add_of_nat: child(kernel, "subNatNat_add_ofNat"),
        sub_nat_nat_add_neg_succ: child(kernel, "subNatNat_add_negSucc"),
        neg_succ_add_sub_nat_nat: child(kernel, "negSucc_add_subNatNat"),
        of_nat_add_neg_of_nat: child(kernel, "ofNat_add_negOfNat"),
        neg_of_nat_add_of_nat: child(kernel, "negOfNat_add_ofNat"),
        neg_of_nat_add_neg_of_nat: child(kernel, "negOfNat_add_negOfNat"),
        neg_of_nat_add_sub_nat_nat: child(kernel, "negOfNat_add_subNatNat"),
        mul_of_nat_neg_of_nat: child(kernel, "mul_ofNat_negOfNat"),
        mul_neg_of_nat_of_nat: child(kernel, "mul_negOfNat_ofNat"),
        mul_neg_succ_neg_of_nat: child(kernel, "mul_negSucc_negOfNat"),
        mul_neg_of_nat_neg_succ: child(kernel, "mul_negOfNat_negSucc"),
        of_nat_mul_sub_nat_nat: child(kernel, "ofNat_mul_subNatNat"),
        neg_succ_mul_sub_nat_nat: child(kernel, "negSucc_mul_subNatNat"),
        le_of_nat_add: child(kernel, "le_ofNat_add"),
        le_dest: child(kernel, "le_dest"),
        lt_of_nat_add: child(kernel, "lt_ofNat_add"),
        lt_dest: child(kernel, "lt_dest"),
        le_of_ofnat_le_ofnat: child(kernel, "le_of_ofNat_le_ofNat"),
        lt_of_ofnat_lt_ofnat: child(kernel, "lt_of_ofNat_lt_ofNat"),
        le_elim,
        lt_elim,
        add: child(kernel, "add"),
        mul: child(kernel, "mul"),
        neg: child(kernel, "neg"),
        sub: child(kernel, "sub"),
        zero: child(kernel, "zero"),
        one: child(kernel, "one"),
        le: le_name,
        lt: lt_name,
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
        add_neg_cancel_right: child(kernel, "add_neg_cancel_right"),
        add_left_neg: child(kernel, "add_left_neg"),
        add_neg_eq_sub: child(kernel, "add_neg_eq_sub"),
        add_left_comm: child(kernel, "add_left_comm"),
        add_mul: child(kernel, "add_mul"),
        add_neg_cancel_left: child(kernel, "add_neg_cancel_left"),
        add_left_cancel: child(kernel, "add_left_cancel"),
        add_left_inj: child(kernel, "add_left_inj"),
        add_lt_add_of_le_of_lt: child(kernel, "add_lt_add_of_le_of_lt"),
        add_le_add_left: child(kernel, "add_le_add_left"),
        add_le_add_right: child(kernel, "add_le_add_right"),
        add_le_add_iff_left: child(kernel, "add_le_add_iff_left"),
        add_le_add_iff_right: child(kernel, "add_le_add_iff_right"),
        add_le_add_three: child(kernel, "add_le_add_three"),
        add_le_iff_le_sub: child(kernel, "add_le_iff_le_sub"),
        add_le_of_le_neg_add: child(kernel, "add_le_of_le_neg_add"),
        add_le_of_le_sub_left: child(kernel, "add_le_of_le_sub_left"),
        add_le_of_le_sub_right: child(kernel, "add_le_of_le_sub_right"),
        mul_le_mul_of_nonneg_left: child(kernel, "mul_le_mul_of_nonneg_left"),
        zero_lt_one: child(kernel, "zero_lt_one"),
        mul_comm: child(kernel, "mul_comm"),
        mul_assoc: child(kernel, "mul_assoc"),
        mul_one: child(kernel, "mul_one"),
        one_mul: child(kernel, "one_mul"),
        neg_one_mul: child(kernel, "neg_one_mul"),
        mul_zero: child(kernel, "mul_zero"),
        left_distrib: child(kernel, "left_distrib"),
        mul_neg: child(kernel, "mul_neg"),
        mul_sub: child(kernel, "mul_sub"),
        mul_nonneg: child(kernel, "mul_nonneg"),
        mul_pos: child(kernel, "mul_pos"),
        sq_nonneg: child(kernel, "sq_nonneg"),
        mul_nonneg_of_nonneg_or_nonpos: child(kernel, "mul_nonneg_of_nonneg_or_nonpos"),
        mul_nonneg_iff: child(kernel, "mul_nonneg_iff"),
        mul_pos_iff: child(kernel, "mul_pos_iff"),
        mul_neg_iff: child(kernel, "mul_neg_iff"),
        mul_nonpos_iff: child(kernel, "mul_nonpos_iff"),
        pow: child(kernel, "pow"),
        pow_zero: child(kernel, "pow_zero"),
        pow_succ: child(kernel, "pow_succ"),
        pow_add: child(kernel, "pow_add"),
        pow_mul: child(kernel, "pow_mul"),
        sum_range: child(kernel, "sumRange"),
        sum_range_zero: child(kernel, "sumRange_zero"),
        sum_range_succ: child(kernel, "sumRange_succ"),
        sum_range_congr: child(kernel, "sumRange_congr"),
        sum_range_add: child(kernel, "sumRange_add"),
        sum_range_neg: child(kernel, "sumRange_neg"),
        sum_range_sub: child(kernel, "sumRange_sub"),
        sum_range_of_nat: child(kernel, "sumRange_ofNat"),
        sum_range_mul_right: child(kernel, "sumRange_mul_right"),
        sum_range_mul_left: child(kernel, "sumRange_mul_left"),
        sum_maps: child(kernel, "sumMaps"),
        sum_maps_zero: child(kernel, "sumMaps_zero"),
        sum_maps_succ: child(kernel, "sumMaps_succ"),
        sum_maps_congr: child(kernel, "sumMaps_congr"),
        sum_maps_mul_left: child(kernel, "sumMaps_mul_left"),
        prod_range_sum_range_expand: child(kernel, "prodRange_sumRange_expand"),
        mod_eq_sum_range: child(kernel, "modEq_sumRange"),
        neg_add: child(kernel, "neg_add"),
        prod_range: child(kernel, "prodRange"),
        prod_range_zero: child(kernel, "prodRange_zero"),
        prod_range_succ: child(kernel, "prodRange_succ"),
        prod_range_shift_front: child(kernel, "prodRange_shiftFront"),
        prod_range_split: child(kernel, "prodRange_split"),
        prod_range_congr: child(kernel, "prodRange_congr"),
        prod_range_congr_lt: child(kernel, "prodRange_congr_lt"),
        prod_range_swap_adjacent: child(kernel, "prodRange_swap_adjacent"),
        prod_range_swap: child(kernel, "prodRange_swap"),
        prod_range_permute: child(kernel, "prodRange_permute"),
        prod_range_mul: child(kernel, "prodRange_mul"),
        prod_range_const_pow: child(kernel, "prodRange_constPow"),
        prod_range_scaled_index_eq_pow_mul_factorial: child(
            kernel,
            "prodRange_scaledIndexEqPowMulFactorial",
        ),
        prod_range_if: child(kernel, "prodRangeIf"),
        prod_range_if_zero: child(kernel, "prodRangeIf_zero"),
        prod_range_if_succ: child(kernel, "prodRangeIf_succ"),
        prod_range_if_permute: child(kernel, "prodRangeIf_permute"),
        gauss_sign_prod_eq_pow_neg_one_of_count: child(kernel, "gaussSignProdEqPowNegOneOfCount"),
        factorial_eq_of_nat_factorial: child(kernel, "factorialEqOfNatFactorial"),
        coprime_factorial_of_lt_prime: child(kernel, "coprimeFactorialOfLtPrime"),
        gauss_term_mod_eq: child(kernel, "gaussTermModEq"),
        gauss_lemma_sign_count: child(kernel, "gaussLemmaSignCount"),
        pow_neg_one_of_even: child(kernel, "pow_neg_one_of_even"),
        pow_neg_one_of_odd: child(kernel, "pow_neg_one_of_odd"),
        second_supplementary_law: child(kernel, "secondSupplementaryLaw"),
        is_quadratic_residue_of_mod_eq: child(kernel, "isQuadraticResidue_of_modEq"),
        wilson_half_split: child(kernel, "wilsonHalfSplit"),
        first_supplementary_law_residue: child(kernel, "firstSupplementaryLawResidue"),
        first_supplementary_law_not_residue: child(kernel, "firstSupplementaryLawNotResidue"),
        no_int_between: child(kernel, "no_int_between"),
        le_total: child(kernel, "le_total"),
        lt_of_le_of_ne: child(kernel, "lt_of_le_of_ne"),
        le_antisymm: child(kernel, "le_antisymm"),
        euclidean_decomposition: child(kernel, "euclidean_decomposition"),
        euclid_of_nat: child(kernel, "euclid_of_nat"),
        euclid_neg_succ: child(kernel, "euclid_neg_succ"),
        ediv: child(kernel, "ediv"),
        emod: child(kernel, "emod"),
        ediv_add_emod: child(kernel, "ediv_add_emod"),
        emod_nonneg: child(kernel, "emod_nonneg"),
        emod_lt_of_pos: child(kernel, "emod_lt_of_pos"),
        emod_natabs_bound: child(kernel, "emod_natAbs_bound"),
        ediv_emod_unique: child(kernel, "ediv_emod_unique"),
        ediv_emod_unique_general: child(kernel, "ediv_emod_unique_general"),
        dvd: child(kernel, "dvd"),
        dvd_refl: child(kernel, "dvd_refl"),
        dvd_trans: child(kernel, "dvd_trans"),
        dvd_add: child(kernel, "dvd_add"),
        dvd_mul_right: child(kernel, "dvd_mul_right"),
        dvd_mul_left: child(kernel, "dvd_mul_left"),
        emod_eq_zero_iff_dvd: child(kernel, "emod_eq_zero_iff_dvd"),
        emod_eq_zero_iff_dvd_general: child(kernel, "emod_eq_zero_iff_dvd_general"),
        mod_eq: child(kernel, "ModEq"),
        mod_eq_refl: child(kernel, "modEq_refl"),
        mod_eq_symm: child(kernel, "modEq_symm"),
        mod_eq_trans: child(kernel, "modEq_trans"),
        mod_eq_iff_dvd: child(kernel, "modEq_iff_dvd"),
        mod_eq_of_nat_mod_eq: child(kernel, "modEq_of_nat_modEq"),
        mod_eq_add_right: child(kernel, "modEq_add_right"),
        mod_eq_add_left: child(kernel, "modEq_add_left"),
        mod_eq_add_left_cancel: child(kernel, "modEq_add_left_cancel"),
        mod_eq_neg: child(kernel, "modEq_neg"),
        neg_mod_eq_neg: child(kernel, "neg_modEq_neg"),
        mod_eq_of_dvd: child(kernel, "modEq_of_dvd"),
        mod_eq_dvd_iff: child(kernel, "modEq_dvd_iff"),
        mod_eq_of_mul_left: child(kernel, "modEq_of_mul_left"),
        mod_eq_of_mul_right: child(kernel, "modEq_of_mul_right"),
        mod_eq_mul_left: child(kernel, "modEq_mul_left"),
        mod_eq_mul_right: child(kernel, "modEq_mul_right"),
        mod_eq_mul: child(kernel, "modEq_mul"),
        mod_eq_cancel: child(kernel, "modEq_cancel"),
        mod_eq_inverse_exists: child(kernel, "modEq_inverse_exists"),
        mod_eq_inverse_unique: child(kernel, "modEq_inverse_unique"),
        mod_eq_pow: child(kernel, "modEq_pow"),
        mod_eq_prod_range: child(kernel, "modEq_prodRange"),
        mod_eq_prod_range_lt: child(kernel, "modEq_prodRange_lt"),
        emod_neg: child(kernel, "emod_neg"),
        mod_eq_of_neg_modulus: child(kernel, "modEq_of_neg_modulus"),
        mod_eq_neg_modulus: child(kernel, "modEq_neg_modulus"),
        mod_eq_one: child(kernel, "modEq_one"),
        mod_eq_add_mul_left: child(kernel, "modEq_add_mul_left"),
        add_mod_eq_left: child(kernel, "add_modEq_left"),
        add_mod_eq_right: child(kernel, "add_modEq_right"),
        mod_mod_eq: child(kernel, "mod_modEq"),
        modulus_mod_eq_zero: child(kernel, "modulus_modEq_zero"),
        mod_eq_sub: child(kernel, "modEq_sub"),
        nat_abs: child(kernel, "natAbs"),
        of_nat_nat_abs_of_nonneg: child(kernel, "of_nat_nat_abs_of_nonneg"),
        nat_abs_neg_of_nat: child(kernel, "nat_abs_neg_of_nat"),
        nat_abs_neg: child(kernel, "nat_abs_neg"),
        nat_abs_pow: child(kernel, "nat_abs_pow"),
        gcd: child(kernel, "gcd"),
        nat_abs_mul: child(kernel, "nat_abs_mul"),
        dvd_of_nat_abs_dvd: child(kernel, "dvd_of_nat_abs_dvd"),
        nat_abs_dvd_nat_abs_of_dvd: child(kernel, "nat_abs_dvd_nat_abs_of_dvd"),
        gcd_dvd_left: child(kernel, "gcd_dvd_left"),
        gcd_dvd_right: child(kernel, "gcd_dvd_right"),
        gcd_comm: child(kernel, "gcd_comm"),
        gcd_one_right: child(kernel, "gcd_one_right"),
        gcd_zero_right: child(kernel, "gcd_zero_right"),
        dvd_gcd: child(kernel, "dvd_gcd"),
        ne_zero_of_gcd: child(kernel, "ne_zero_of_gcd"),
        gcd_eq_one_of_gcd_mul_right_eq_one_left: child(
            kernel,
            "gcd_eq_one_of_gcd_mul_right_eq_one_left",
        ),
        gcd_eq_one_of_gcd_mul_right_eq_one_right: child(
            kernel,
            "gcd_eq_one_of_gcd_mul_right_eq_one_right",
        ),
        dvd_mul_split: child(kernel, "dvd_mul_split"),
        gcd_eq_gcd_ab: child(kernel, "gcd_eq_gcd_ab"),
        xgcd_aux: kernel.name_str(nat_root, "xgcdAux"),
        nat_gcd_a: kernel.name_str(nat_root, "gcdA"),
        nat_gcd_b: kernel.name_str(nat_root, "gcdB"),
        xgcd_aux_sound: kernel.name_str(nat_root, "xgcdAux_sound"),
        nat_gcd_eq_gcd_ab: kernel.name_str(nat_root, "gcd_eq_gcd_ab"),
        exists_mul_mod_eq_gcd: kernel.name_str(nat_root, "exists_mul_mod_eq_gcd"),
        gcd_a: child(kernel, "gcdA"),
        gcd_b: child(kernel, "gcdB"),
        gcd_eq_gcd_ab_witnesses: child(kernel, "gcd_eq_gcd_ab_witnesses"),
        gcd_div_gcd_div_gcd: child(kernel, "gcd_div_gcd_div_gcd"),
        gcd_div: child(kernel, "gcd_div"),
        coprime: child(kernel, "Coprime"),
        coprime_of_bezout_one: child(kernel, "coprime_of_bezout_one"),
        gauss_lemma: child(kernel, "gauss_lemma"),
        dvd_of_dvd_mul_right_of_gcd_one: child(kernel, "dvd_of_dvd_mul_right_of_gcd_one"),
        dvd_of_dvd_mul_left_of_gcd_one: child(kernel, "dvd_of_dvd_mul_left_of_gcd_one"),
        gcd_greatest: child(kernel, "gcd_greatest"),
        euclid_lemma: child(kernel, "euclid_lemma"),
        euclid_infinitude: child(kernel, "euclid_infinitude"),
        prime_dvd_mul_prime: child(kernel, "prime_dvd_mul'"),
        prime_dvd_mul: child(kernel, "prime_dvd_mul"),
        not_prime_of_int_mul: child(kernel, "not_prime_of_int_mul"),
        gcd_ne_one_iff_gcd_mul_right_ne_one: child(kernel, "gcd_ne_one_iff_gcd_mul_right_ne_one"),
        succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul: child(
            kernel,
            "succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul",
        ),
        crt_exists: child(kernel, "crt_exists"),
        crt_unique: child(kernel, "crt_unique"),
        rat,
        rat_mk: kernel.name_str(rat, "mk"),
        rat_normalize: kernel.name_str(rat, "normalize"),
        rat_rec: kernel.name_str(rat, "rec"),
        rat_num: kernel.name_str(rat, "num"),
        rat_den: kernel.name_str(rat, "den"),
        rat_den_pos: kernel.name_str(rat, "den_pos"),
        rat_mul: kernel.name_str(rat, "mul"),
        rat_reduced: kernel.name_str(rat, "reduced"),
        rat_neg: kernel.name_str(rat, "neg"),
        rat_add: kernel.name_str(rat, "add"),
        eq_em: child(kernel, "eq_em"),
        is_comm_ring: child(kernel, "IsCommRing"),
        int_is_comm_ring: child(kernel, "int_isCommRing"),
        mul_eq_zero: child(kernel, "mul_eq_zero"),
        factorial: child(kernel, "factorial"),
        factorial_zero: child(kernel, "factorial_zero"),
        factorial_succ: child(kernel, "factorial_succ"),
        self_inverse_mod_prime: child(kernel, "self_inverse_mod_prime"),
        factorial_pos: child(kernel, "factorial_pos"),
        of_nat_pow: child(kernel, "of_nat_pow"),
        pow_prime_sub_one_modeq_one: child(kernel, "pow_prime_sub_one_modeq_one"),
        mul_inv_of_pow: child(kernel, "mul_inv_of_pow"),
        inverse_index: kernel.name_str(nat_root, "inverseIndex"),
        inverse_index_maps_into: kernel.name_str(nat_root, "inverseIndex_maps_into"),
        inverse_index_injective: kernel.name_str(nat_root, "inverseIndex_injective"),
        inverse_index_fixed_point: kernel.name_str(nat_root, "inverseIndex_fixed_point"),
        inverse_index_involutive: kernel.name_str(nat_root, "inverseIndex_involutive"),
        inverse_index_fixes_zero: kernel.name_str(nat_root, "inverseIndex_fixes_zero"),
        inverse_index_fixes_last: kernel.name_str(nat_root, "inverseIndex_fixes_last"),
        inverse_index_interior_fixed_point_free: kernel
            .name_str(nat_root, "inverseIndex_interior_fixed_point_free"),
        factorial_sq_modeq_one: child(kernel, "factorial_sq_modeq_one"),
        prod_range_pairing_collapse: child(kernel, "prod_range_pairing_collapse"),
        factorial_interior_modeq_one: child(kernel, "factorial_interior_modeq_one"),
        wilson: child(kernel, "wilson"),
        dvd_factorial_of_le: child(kernel, "dvd_factorial_of_le"),
        wilson_converse: child(kernel, "wilson_converse"),
        wilson_iff: child(kernel, "wilson_iff"),
        is_quadratic_residue: child(kernel, "is_quadratic_residue"),
        is_quadratic_residue_one: child(kernel, "is_quadratic_residue_one"),
        is_quadratic_residue_mul: child(kernel, "is_quadratic_residue_mul"),
        euler_criterion_pm_one: child(kernel, "euler_criterion_pm_one"),
        euler_criterion_residue_imp_one: child(kernel, "euler_criterion_residue_imp_one"),
        euler_criterion_neg_one_imp_not_residue: child(
            kernel,
            "euler_criterion_neg_one_imp_not_residue",
        ),
        euler_unit_coprime: child(kernel, "euler_unit_coprime"),
        euler_unit_coprime_iff: child(kernel, "euler_unit_coprime_iff"),
        euler_unit_perm_injective: child(kernel, "euler_unit_perm_injective"),
        euler_unit_perm_maps_into: child(kernel, "euler_unit_perm_maps_into"),
        prod_range_if_const_eq_pow_count: child(kernel, "prodRangeIf_const_eq_pow_count"),
        prod_range_if_coprime: child(kernel, "prodRangeIf_coprime"),
        prod_range_if_factor_const_left: child(kernel, "prodRangeIf_factor_const_left"),
        prod_range_if_modeq: child(kernel, "prodRangeIf_modeq"),
        euler_totient_theorem: child(kernel, "euler_totient_theorem"),
        euler_unit_injective: child(kernel, "euler_unit_injective"),
        fib_cassini: child(kernel, "fib_cassini"),
        fib: child(kernel, "fib"),
        fib_two_mul_add_one_pos: child(kernel, "fib_two_mul_add_one_pos"),
        even: child(kernel, "Even"),
        odd: child(kernel, "Odd"),
        odd_iff_nat_abs_odd: child(kernel, "odd_iff_nat_abs_odd"),
        even_iff_nat_abs_even: child(kernel, "even_iff_nat_abs_even"),
        emod_two_eq_zero_or_one: child(kernel, "emod_two_eq_zero_or_one"),
        emod_two_ne_zero: child(kernel, "emod_two_ne_zero"),
        emod_two_ne_one: child(kernel, "emod_two_ne_one"),
        ediv_two_mul_two_of_even: child(kernel, "ediv_two_mul_two_of_even"),
        ediv_two_mul_two_add_one_of_odd: child(kernel, "ediv_two_mul_two_add_one_of_odd"),
        add_one_ediv_two_mul_two_of_odd: child(kernel, "add_one_ediv_two_mul_two_of_odd"),
        odd_of_mul_left: child(kernel, "odd_of_mul_left"),
        odd_of_mul_right: child(kernel, "odd_of_mul_right"),
        even_add: child(kernel, "even_add"),
        even_add_prime: child(kernel, "even_add'"),
        even_add_one: child(kernel, "even_add_one"),
        fib_of_odd: child(kernel, "fib_of_odd"),
        induction_on: child(kernel, "induction_on"),
        fib_rec: child(kernel, "fib_rec"),
        fib_add: child(kernel, "fib_add"),
        fib_two_mul: child(kernel, "fib_two_mul"),
        fib_two_mul_add_two: child(kernel, "fib_two_mul_add_two"),

        // `int-dvd-mirrors` lane -- see the matching struct-field block above.
        dvd_gcd_nat: child(kernel, "dvd_gcd_nat"),
        dvd_gcd_nat_iff: child(kernel, "dvd_gcd_nat_iff"),
        dvd_coe_gcd_iff: child(kernel, "dvd_coe_gcd_iff"),
        gcd_dvd_iff: child(kernel, "gcd_dvd_iff"),
        exists_gcd_one: child(kernel, "exists_gcd_one"),
        exists_gcd_one_prime: child(kernel, "exists_gcd_one'"),
        ediv_gcd_ne_zero_of_ne_zero_left: child(kernel, "ediv_gcd_ne_zero_of_ne_zero_left"),
        ediv_gcd_ne_zero_if_ne_zero_right: child(kernel, "ediv_gcd_ne_zero_if_ne_zero_right"),
        mod_eq_add: child(kernel, "mod_eq_add"),
        mod_eq_add_right_cancel: child(kernel, "mod_eq_add_right_cancel"),
        mod_eq_add_left_cancel_general: child(kernel, "mod_eq_add_left_cancel_general"),
        mod_eq_add_right_cancel_general: child(kernel, "mod_eq_add_right_cancel_general"),
        mod_eq_dvd: child(kernel, "mod_eq_dvd"),
        mod_eq_emod_eq: child(kernel, "mod_eq_emod_eq"),
        mod_eq_mul_general: child(kernel, "mod_eq_mul_general"),

        // `int-gcd-mul-transport` lane -- see the matching struct-field block
        // above.
        dvd_gcd_mul_iff_dvd_mul: child(kernel, "dvd_gcd_mul_iff_dvd_mul"),
        dvd_mul_gcd_iff_dvd_mul: child(kernel, "dvd_mul_gcd_iff_dvd_mul"),
        dvd_gcd_mul_gcd_iff_dvd_mul: child(kernel, "dvd_gcd_mul_gcd_iff_dvd_mul"),
        mod_eq_cancel_left_div_gcd: child(kernel, "mod_eq_cancel_left_div_gcd"),
        mod_eq_cancel_right_div_gcd: child(kernel, "mod_eq_cancel_right_div_gcd"),
    }
}

/// Build the integer prelude: `ℤ` **constructed** over the proved `ℕ`
/// development, and — since 2026-08-16 — asserting nothing.
///
/// The undischarged remainder used to be a list kept as data so it shrank
/// visibly. It reached zero when `Int.euclidean_decomposition` became a theorem
/// (see the private `euclid` submodule), so the list, its type alias, and `IntDev::int_axiom` are
/// gone with it; `int_prelude_tests::asserted_laws` is now empty and guards
/// against one reappearing.
///
/// The build is **atomic and cached**: a second call on the same kernel returns
/// the same handles without re-declaring, and any failure rolls back every
/// `Int` declaration this invocation admitted.
///
/// # Errors
///
/// Returns the trusted gate's rejection or an exact-package conflict. A failed
/// Int build leaves the pre-call environment unchanged.
pub fn build_int_prelude(kernel: &mut Kernel) -> Result<IntPrelude, KernelError> {
    if let Some(PreludeValue::Int(prelude)) =
        crate::prelude_cache::try_restore(kernel, PreludeKey::Int)
    {
        return Ok(*prelude);
    }
    build_int_prelude_uncached(kernel)
}

/// [`build_int_prelude`] without the process-wide template fast path.
///
/// This is the route that actually runs the trusted gate, and the one the
/// template itself is built through (ADR-0464).
pub(crate) fn build_int_prelude_uncached(kernel: &mut Kernel) -> Result<IntPrelude, KernelError> {
    let nat = build_nat_prelude(kernel)?;
    if let Some(PreludeValue::Int(prelude)) = kernel.cached_prelude(PreludeKey::Int)? {
        return Ok(*prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<IntPrelude, KernelError> {
        let prelude = intern_names(kernel, nat);
        let mut d = IntDev::new(kernel, prelude);
        defs::declare_carrier(&mut d)?;
        defs::declare_normalizers(&mut d)?;
        defs::declare_operations(&mut d)?;
        defs::declare_order_definitions(&mut d)?;
        sub_nat_nat::declare_borrow_lemmas(&mut d)?;
        order::declare_order_theorems(&mut d)?;
        algebra::declare_algebra_theorems(&mut d)?;
        sub_nat_nat::declare_add_lemmas(&mut d)?;
        algebra::declare_add_assoc(&mut d)?;
        sign::declare_sign_lemmas(&mut d)?;
        sign::declare_neg_one_mul(&mut d)?;
        sign::declare_mul_assoc(&mut d)?;
        defs::declare_pow(&mut d)?;
        defs::declare_pow_equations(&mut d)?;
        algebra::declare_pow_add(&mut d)?;
        algebra::declare_pow_mul(&mut d)?;
        sub_nat_nat::declare_mul_lemmas(&mut d)?;
        algebra::declare_left_distrib(&mut d)?;
        sub::declare_sub_definition(&mut d)?;
        sub::declare_mul_neg(&mut d)?;
        sub::declare_mul_sub(&mut d)?;
        add_basics::declare_add_basics(&mut d)?;
        order::declare_difference_lemmas(&mut d)?;
        order_coercion::declare_ofnat_order_coercions(&mut d)?;
        order_coercion::declare_dest_elim(&mut d)?;
        order::declare_additive_order(&mut d)?;
        order_add::declare_add_le_add_left_right(&mut d)?;
        order_add::declare_add_le_add_iff(&mut d)?;
        order_add::declare_add_le_add_three(&mut d)?;
        order_add::declare_add_le_iff_le_sub(&mut d)?;
        order_add::declare_add_le_of_le_sub(&mut d)?;
        decide::declare_decidable_equality(&mut d)?;
        order::declare_le_antisymm(&mut d)?;
        algebra::declare_ordered_multiplication(&mut d)?;
        euclid::declare_of_nat_branch(&mut d)?;
        euclid::declare_neg_succ_branch(&mut d)?;
        euclid::declare_decomposition(&mut d)?;
        division::declare_ediv(&mut d)?;
        division::declare_emod(&mut d)?;
        sub_nat_nat::declare_neg_of_nat_add_sub_nat_nat(&mut d)?;
        division::declare_ediv_add_emod(&mut d)?;
        division::declare_emod_nonneg(&mut d)?;
        division::declare_emod_lt_of_pos(&mut d)?;
        division::declare_ediv_emod_unique(&mut d)?;
        dvd::declare_dvd_definition(&mut d)?;
        dvd::declare_dvd_refl(&mut d)?;
        dvd::declare_dvd_mul_right(&mut d)?;
        dvd::declare_dvd_mul_left(&mut d)?;
        dvd::declare_dvd_trans(&mut d)?;
        dvd::declare_dvd_add(&mut d)?;
        dvd::declare_emod_eq_zero_iff_dvd(&mut d)?;
        modeq::declare_modeq_definition(&mut d)?;
        modeq::declare_modeq_refl(&mut d)?;
        modeq::declare_modeq_symm(&mut d)?;
        modeq::declare_modeq_trans(&mut d)?;
        modeq::declare_modeq_iff_dvd(&mut d)?;
        // Moved ahead of the rest of `modeq_family`'s block (their original
        // position, after `modeq::declare_modeq_pow`): `modeq_to_dvd`'s
        // converse `dvd_to_modeq` (used by `declare_modeq_add_right` and
        // every generalized law below it) is built on
        // `modEq_add_mul_left`, which itself needs `emod_neg`/
        // `modEq_neg_modulus`. `declare_modeq_of_neg_modulus` does not gate
        // anything below and stays in its original spot.
        modeq_family::declare_emod_neg(&mut d)?;
        modeq_family::declare_modeq_neg_modulus(&mut d)?;
        modeq_family::declare_modeq_add_mul_left(&mut d)?;
        modeq::declare_modeq_of_nat_modeq(&mut d)?;
        modeq::declare_modeq_add_right(&mut d)?;
        modeq::declare_modeq_add_left(&mut d)?;
        modeq::declare_modeq_add_left_cancel(&mut d)?;
        modeq::declare_modeq_neg(&mut d)?;
        modeq::declare_neg_modeq_neg(&mut d)?;
        modeq::declare_modeq_of_dvd(&mut d)?;
        modeq::declare_modeq_dvd_iff(&mut d)?;
        modeq::declare_modeq_of_mul_left(&mut d)?;
        modeq_family::declare_modeq_of_mul_right(&mut d)?;
        modeq::declare_modeq_mul_left(&mut d)?;
        modeq::declare_modeq_mul_right(&mut d)?;
        modeq::declare_modeq_mul(&mut d)?;
        modeq::declare_modeq_pow(&mut d)?;
        modeq_family::declare_modeq_of_neg_modulus(&mut d)?;
        modeq_family::declare_modeq_one(&mut d)?;
        modeq_family::declare_add_modeq_left(&mut d)?;
        modeq_family::declare_add_modeq_right(&mut d)?;
        modeq_family::declare_mod_modeq(&mut d)?;
        modeq_family::declare_modulus_modeq_zero(&mut d)?;
        modeq_family::declare_modeq_sub(&mut d)?;
        prod::declare_prod_range(&mut d)?;
        prod::declare_prod_range_equations(&mut d)?;
        prod::declare_prod_range_shift_front(&mut d)?;
        prod::declare_prod_range_split(&mut d)?;
        prod::declare_prod_range_congr(&mut d)?;
        prod::declare_prod_range_congr_lt(&mut d)?;
        prod::declare_prod_range_swap_adjacent(&mut d)?;
        prod::declare_prod_range_swap(&mut d)?;
        prod::declare_prod_range_permute(&mut d)?;
        prod::declare_prod_range_mul(&mut d)?;
        prod::declare_prod_range_const_pow(&mut d)?;
        prod::declare_modeq_prod_range(&mut d)?;
        prod::declare_modeq_prod_range_lt(&mut d)?;
        // The signed finite sum (ADR-1260's named obstruction for Eisenstein's
        // lemma). Placed immediately after the product family because it needs
        // the same prerequisites plus the `ModEq` congruences declared above:
        // `add_assoc`/`add_comm`/`add_zero` (`add_basics`, `algebra`),
        // `neg_one_mul`/`left_distrib` for `neg_add`, and
        // `modEq_refl`/`trans`/`add_right`/`add_left` for `modEq_sumRange`.
        sum::declare_neg_add(&mut d)?;
        sum::declare_sum_range(&mut d)?;
        sum::declare_sum_range_equations(&mut d)?;
        sum::declare_sum_range_congr(&mut d)?;
        sum::declare_sum_range_add(&mut d)?;
        sum::declare_sum_range_neg(&mut d)?;
        sum::declare_sum_range_sub(&mut d)?;
        sum::declare_sum_range_of_nat(&mut d)?;
        sum::declare_modeq_sum_range(&mut d)?;
        // The function-space-indexed sum and the generalized distributive law
        // (ADR-1310). Needs `Int.sumRange` + its `congr` (immediately above),
        // `Int.prodRange_shiftFront` (above), and the ring lemmas `add_mul`,
        // `left_distrib`, `mul_zero`, `mul_comm` (`algebra`, far above).
        sum_maps::declare_sum_range_mul_right(&mut d)?;
        sum_maps::declare_sum_range_mul_left(&mut d)?;
        sum_maps::declare_sum_maps(&mut d)?;
        sum_maps::declare_sum_maps_equations(&mut d)?;
        sum_maps::declare_sum_maps_congr(&mut d)?;
        sum_maps::declare_sum_maps_mul_left(&mut d)?;
        sum_maps::declare_prod_range_sum_range_expand(&mut d)?;
        wilson::declare_factorial(&mut d)?;
        wilson::declare_factorial_equations(&mut d)?;
        gauss_factorial_product::declare_prod_range_scaled_index_eq_pow_mul_factorial(&mut d)?;
        // Item 2 of Gauss's-lemma connecting theorem (ADR-1070): the
        // `Int.factorial`/`Nat.factorial` bridge. Needs only `Int.factorial`,
        // `Nat.factorial` (far above) and `Int.one := ofNat 1` defeq --
        // nothing from `natAbs`/`gcd`/`Coprime`, so it can sit here rather
        // than waiting for them.
        gauss_factorial_coprime::declare_factorial_eq_of_nat_factorial(&mut d)?;
        nat_abs::declare_nat_abs(&mut d)?;
        // Needs `Int.natAbs`, just declared above -- `declare_emod_lt_of_pos`
        // (built well before `natAbs` exists) is why this sign-general bound
        // could not sit beside its sibling `emod_nonneg`/`emod_lt_of_pos`
        // theorems higher up this list.
        division::declare_emod_natabs_bound(&mut d)?;
        // Also needs `Int.natAbs`, and `Int.ediv_emod_unique` (declared much
        // higher up, before `natAbs` existed) -- same reason this cannot sit
        // beside its own sibling either.
        division::declare_ediv_emod_unique_general(&mut d)?;
        // Needs both `emod_natabs_bound` and `ediv_emod_unique_general`,
        // just declared above -- same build-order constraint as they carry
        // relative to `Int.natAbs`.
        dvd::declare_emod_eq_zero_iff_dvd_general(&mut d)?;
        nat_abs::declare_nat_abs_lemmas(&mut d)?;
        nat_abs::declare_nat_abs_neg_of_nat(&mut d)?;
        nat_abs::declare_nat_abs_neg(&mut d)?;
        parity::declare_parity_all(&mut d)?;
        parity::declare_emod_two_eq_zero_or_one(&mut d)?;
        parity::declare_emod_two_ne_zero(&mut d)?;
        parity::declare_emod_two_ne_one(&mut d)?;
        parity::declare_ediv_two_mul_two_of_even(&mut d)?;
        parity::declare_ediv_two_mul_two_add_one_of_odd(&mut d)?;
        parity::declare_add_one_ediv_two_mul_two_of_odd(&mut d)?;
        gcd::declare_gcd(&mut d)?;
        gcd::declare_gcd_comm(&mut d)?;
        gcd::declare_gcd_one_zero_right(&mut d)?;
        gcd::declare_nat_abs_mul(&mut d)?;
        parity::declare_odd_of_mul_left(&mut d)?;
        parity::declare_odd_of_mul_right(&mut d)?;
        // The `emod` additive law and the three `ml430-int-even-add-*`
        // mirrors (int-emod-additive lane, 2026-08-29). Needs `Int.ModEq`'s
        // `mod_eq_add_right`/`mod_eq_add_left`/`mod_eq_trans` (`modeq.rs`,
        // declared much earlier) -- already satisfied by this point.
        parity::declare_even_add(&mut d)?;
        parity::declare_even_add_prime(&mut d)?;
        parity::declare_even_add_one(&mut d)?;
        nat_abs::declare_nat_abs_pow(&mut d)?;
        gcd::declare_dvd_of_nat_abs_dvd(&mut d)?;
        gcd::declare_nat_abs_dvd_nat_abs_of_dvd(&mut d)?;
        gcd::declare_gcd_dvd_left_right(&mut d)?;
        gcd::declare_dvd_gcd(&mut d)?;
        gcd::declare_ne_zero_of_gcd(&mut d)?;
        gcd::declare_gcd_eq_one_of_gcd_mul_right_eq_one(&mut d)?;
        gcd::declare_gcd_eq_gcd_ab(&mut d)?;
        bezout_witnesses::declare_xgcd_aux(&mut d)?;
        bezout_witnesses::declare_int_gcd_ab(&mut d)?;
        bezout_witnesses::declare_xgcd_aux_sound(&mut d)?;
        bezout_witnesses::declare_nat_gcd_eq_gcd_ab(&mut d)?;
        gcd::declare_exists_mul_mod_eq_gcd(&mut d)?;
        bezout_witnesses::declare_gcd_eq_gcd_ab_witnesses(&mut d)?;
        gcd::declare_gcd_div_gcd_div_gcd(&mut d)?;
        gcd::declare_gcd_div(&mut d)?;
        gcd::declare_coprime(&mut d)?;
        // Item 2 of Gauss's-lemma connecting theorem (ADR-1070): the
        // `Int`-typed coprimality of `m!` with `pp`, needed by item 3's
        // `Int.ModEq.cancel`. Needs `Int.Coprime`/`Int.natAbs`, just declared.
        gauss_factorial_coprime::declare_coprime_factorial_of_lt_prime(&mut d)?;
        gcd::declare_coprime_of_bezout_one(&mut d)?;
        gcd::declare_gauss_lemma(&mut d)?;
        gcd::declare_dvd_of_dvd_mul_right_of_gcd_one(&mut d)?;
        gcd::declare_dvd_of_dvd_mul_left_of_gcd_one(&mut d)?;
        gcd::declare_gcd_greatest(&mut d)?;
        modeq::declare_modeq_cancel(&mut d)?;
        gcd::declare_modeq_inverse_exists(&mut d)?;
        modinv::declare_modeq_inverse_unique(&mut d)?;
        gcd::declare_euclid_lemma(&mut d)?;
        gcd::declare_euclid_infinitude(&mut d)?;
        wilson::declare_self_inverse_mod_prime(&mut d)?;
        wilson::declare_factorial_pos(&mut d)?;
        wilson::declare_of_nat_pow(&mut d)?;
        wilson::declare_pow_prime_sub_one_modeq_one(&mut d)?;
        wilson::declare_mul_inv_of_pow(&mut d)?;
        wilson::declare_inverse_index(&mut d)?;
        wilson::declare_inverse_index_maps_into(&mut d)?;
        wilson::declare_inverse_index_injective(&mut d)?;
        wilson::declare_inverse_index_fixed_point(&mut d)?;
        wilson::declare_inverse_index_involutive(&mut d)?;
        wilson::declare_inverse_index_fixes_zero(&mut d)?;
        wilson::declare_inverse_index_fixes_last(&mut d)?;
        wilson::declare_inverse_index_interior_fixed_point_free(&mut d)?;
        wilson::declare_factorial_sq_modeq_one(&mut d)?;
        wilson::declare_prod_range_pairing_collapse(&mut d)?;
        wilson::declare_factorial_interior_modeq_one(&mut d)?;
        wilson::declare_wilson(&mut d)?;
        wilson::declare_dvd_factorial_of_le(&mut d)?;
        wilson::declare_wilson_converse(&mut d)?;
        wilson::declare_wilson_iff(&mut d)?;
        euler::declare_is_quadratic_residue(&mut d)?;
        euler::declare_is_quadratic_residue_one(&mut d)?;
        euler::declare_is_quadratic_residue_mul(&mut d)?;
        euler::declare_euler_criterion_pm_one(&mut d)?;
        qr_criterion::declare_euler_criterion_residue_imp_one(&mut d)?;
        qr_criterion::declare_euler_criterion_neg_one_imp_not_residue(&mut d)?;
        euler_totient::declare_euler_unit_coprime(&mut d)?;
        euler_totient::declare_euler_unit_injective(&mut d)?;
        euler_unit_preserve::declare_euler_unit_coprime_iff(&mut d)?;
        euler_unit_range::declare_euler_unit_perm_injective(&mut d)?;
        euler_unit_range::declare_euler_unit_perm_maps_into(&mut d)?;
        euler_theorem::declare_prod_range_if_all(&mut d)?;
        euler_prod_pow::declare_prod_range_if_const_eq_pow_count(&mut d)?;
        euler_prod_coprime::declare_prod_range_if_coprime(&mut d)?;
        euler_prod_factor::declare_prod_range_if_factor_const_left(&mut d)?;
        euler_prod_modeq::declare_prod_range_if_modeq(&mut d)?;
        euler_assembly::declare_euler_totient_theorem(&mut d)?;
        gauss_sign_product::declare_gauss_sign_prod_eq_pow_neg_one_of_count(&mut d)?;
        gauss_term_congruence::declare_gauss_term_mod_eq(&mut d)?;
        gauss_assembly::declare_gauss_lemma(&mut d)?;
        // The second supplementary law of quadratic reciprocity (ADR-1150):
        // needs `gaussLemmaSignCount` (just above), `Nat.half_ceil_parity`,
        // `Nat.gaussNegCountTwoClosedForm` and `Nat.coprime_two_left` (all in
        // the Nat prelude), plus `fibonacci.rs`'s `pow_neg_one_*` helpers.
        second_supplementary::declare_second_supplementary_all(&mut d)?;
        // The first supplementary law of quadratic reciprocity, non-residue
        // half (ADR-1230): needs `euler_criterion_neg_one_imp_not_residue`
        // (`qr_criterion.rs`) plus `second_supplementary.rs`'s
        // `pow_neg_one_of_odd` and `two_mul_eq_add_self`.
        first_supplementary::declare_first_supplementary_all(&mut d)?;
        // The RESIDUE half (ADR-1235): needs `Int.wilson`, `prodRange_split`,
        // `prodRange_permute` at the reflection, and `Nat.sub_sub_self`.
        first_supplementary_residue::declare_first_supplementary_residue_all(&mut d)?;
        crt::declare_crt_exists(&mut d)?;
        crt::declare_crt_unique(&mut d)?;
        two_sided_induction::declare_induction_on(&mut d)?;
        fibonacci::declare_fib_cassini_all(&mut d)?;
        fibonacci::declare_fib(&mut d)?;
        fibonacci::declare_fib_two_mul_add_one_pos(&mut d)?;
        fibonacci::declare_fib_of_odd(&mut d)?;
        fibonacci::declare_fib_rec(&mut d)?;
        fibonacci::declare_fib_add(&mut d)?;
        fibonacci::declare_fib_two_mul(&mut d)?;
        fibonacci::declare_fib_two_mul_add_two(&mut d)?;
        rat::declare_rat(&mut d)?;
        rat::declare_normalize(&mut d)?;
        rat::declare_arithmetic(&mut d)?;
        rat::declare_more_arithmetic(&mut d)?;
        ring::declare_ring_all(&mut d, &prelude)?;
        // Needs `Int.mul_eq_zero`, declared inside `declare_ring_all` just
        // above -- the sign-of-a-product family's `Iff` forward directions
        // resolve a mixed-sign quadrant to "the product is exactly zero" and
        // then decide which factor vanishes.
        sign_product::declare_sign_product_theorems(&mut d)?;
        // `int-dvd-mirrors` lane: `ml430` divisibility/gcd/`ModEq` mirrors.
        // Placed last so every lemma it composes (gcd/dvd/modeq family) is
        // already declared.
        dvd_gcd_mirrors::declare_all(&mut d)?;
        // `int-gcd-mul-transport` lane: the ℤ transport of
        // `nat_prelude/gcd_mul_right_mirrors.rs`'s three mirrors. Needs
        // `gcd.rs` (`Int.gcd`, `nat_abs_mul`, the `natAbs`/`dvd` bridges) and
        // the `Nat` prelude's `dvd_gcd_mul_iff_dvd_mul`/
        // `dvd_mul_gcd_iff_dvd_mul` (always already built, since `Nat`'s
        // prelude is a dependency of `Int`'s). Placed last for the same
        // reason as `dvd_gcd_mirrors` just above.
        gcd_scaled_mirrors::declare_all(&mut d)?;
        // `modeq-div-gcd` lane: the div-by-gcd `ModEq` cancellation mirrors.
        // Needs `Int.gcd_div_gcd_div_gcd`/`Int.gauss_lemma`/`Int.mul_eq_zero`
        // (all declared above) and `modeq.rs`'s `modeq_to_dvd`/`dvd_to_modeq`
        // bridge. Placed last for the same reason `dvd_gcd_mirrors` is.
        modeq_cancel_div_gcd::declare_all(&mut d)?;
        // `int-dvd-mul-split` lane: `ml430`'s `Int.dvd_mul`. Needs `gcd.rs`
        // (`Int.gcd`, `gcd_dvd_left`/`gcd_dvd_right`, the `natAbs`/`dvd`
        // bridges), `ring.rs` (`Int.mul_eq_zero`), and the `Nat` prelude's
        // `dvd_gcd`/`gcd_mul_right`/`eq_zero_of_gcd_eq_zero_left`/
        // `zero_lt_of_ne_zero` (always already built). Placed last for the
        // same reason as the two mirror modules just above.
        dvd_mul_split::declare_dvd_mul_split(&mut d)?;
        // `draw11-theorems-e` lane: `Int.gcd_dvd_iff`, an `ml430` mirror.
        // Needs `gcd_eq_gcd_ab_witnesses` (`bezout_witnesses.rs`),
        // `gcd_dvd_left`/`gcd_dvd_right`/`nat_abs_dvd_nat_abs_of_dvd`
        // (`gcd.rs`), and `dvd_trans`/`dvd_add`/`dvd_mul_right` (`dvd.rs`),
        // all declared above. Placed last for the same reason as the mirror
        // modules above it.
        gcd_dvd_iff::declare_gcd_dvd_iff(&mut d)?;
        // `draw11-theorems-e` lane: `Int.exists_gcd_one`/`exists_gcd_one'`,
        // two more `ml430` mirrors. Needs `gcd_div_gcd_div_gcd`,
        // `gcd_dvd_left`/`gcd_dvd_right`, `emod_eq_zero_iff_dvd`,
        // `ediv_add_emod` (all `gcd.rs`/`dvd.rs`, declared above). Placed
        // last for the same reason as the mirror modules above it.
        exists_gcd_one::declare_exists_gcd_one(&mut d)?;
        exists_gcd_one::declare_exists_gcd_one_prime(&mut d)?;
        // `int-prime-dvd` lane: three `ml430` mirrors built directly from
        // `gcd::declare_euclid_lemma` (`prime_dvd_mul'`, `prime_dvd_mul`) and
        // from `Nat.not_prime_of_dvd_of_ne`/`Nat.prime_ne_zero`
        // (`not_prime_of_int_mul`). Placed last for the same reason as the
        // mirror modules above it.
        prime_dvd_mul_mirrors::declare_prime_dvd_mul_prime(&mut d)?;
        prime_dvd_mul_mirrors::declare_prime_dvd_mul(&mut d)?;
        prime_dvd_mul_mirrors::declare_not_prime_of_int_mul(&mut d)?;
        prime_dvd_mul_mirrors::declare_gcd_ne_one_iff_gcd_mul_right_ne_one(&mut d)?;
        prime_dvd_mul_mirrors::declare_succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul(&mut d)?;
        Ok(prelude)
    })();
    match built {
        Ok(prelude) => {
            kernel.register_prelude(
                PreludeKey::Int,
                PreludeValue::Int(Box::new(prelude)),
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
mod int_prelude_tests;

#[cfg(test)]
mod sum_maps_tests;
