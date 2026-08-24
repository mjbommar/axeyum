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

mod algebra;
mod crt;
mod decide;
mod defs;
mod division;
mod dvd;
mod euclid;
mod gcd;
mod modeq;
mod modeq_family;
mod modinv;
mod nat_abs;
pub(crate) mod ops;
mod order;
mod prod;
mod rat;
mod sign;
mod statements;
mod sub;
mod sub_nat_nat;
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
    /// `add_lt_add_of_le_of_lt :
    /// ∀ (a b c d : Int), le a b → lt c d → lt (add a c) (add b d)`.
    pub add_lt_add_of_le_of_lt: NameId,

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
    /// `prodRange_zero : ∀ f, Eq Int (prodRange f zero) one` — closes by
    /// `Eq.refl`.
    pub prod_range_zero: NameId,
    /// `prodRange_succ : ∀ f n, Eq Int (prodRange f (succ n)) (mul (prodRange f n) (f n))`
    /// — closes by `Eq.refl`.
    pub prod_range_succ: NameId,
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
    /// `ediv_emod_unique : ∀ a b q1 r1 q2 r2,
    /// 0 < b → a = b*q1+r1 → 0 ≤ r1 → r1 < b →
    /// a = b*q2+r2 → 0 ≤ r2 → r2 < b → q1 = q2 ∧ r1 = r2` — the division
    /// algorithm's uniqueness for a **positive** divisor: any two
    /// quotient/remainder pairs reconstructing the same dividend with
    /// remainders in `[0, b)` agree.
    pub ediv_emod_unique: NameId,

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
    /// `ModEq.add_right : ∀ n a b c, 0 < n → ModEq n a b → ModEq n (a+c) (b+c)`.
    pub mod_eq_add_right: NameId,
    /// `ModEq.add_left : ∀ n a b c, 0 < n → ModEq n a b → ModEq n (c+a) (c+b)`.
    pub mod_eq_add_left: NameId,
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
    /// `gcd_eq_gcd_ab : ∀ a b, ∃ u v, ofNat (gcd a b) = a*u + b*v` — Bézout's
    /// identity over `ℤ` (Elements VII.2, strong form), transported from
    /// `Nat.gcd_bezout` through `natAbs`.
    pub gcd_eq_gcd_ab: NameId,
    /// `Int.Coprime a b := Eq Nat (gcd a b) 1` — the converse of Bézout
    /// (Elements VII, Def. 12), stated over the `Nat`-valued `gcd`.
    pub coprime: NameId,
    /// `coprime_of_bezout_one : ∀ a b u v, Eq Int (a*u+b*v) one → Coprime a b`.
    pub coprime_of_bezout_one: NameId,
    /// `gauss_lemma : ∀ a b c, Coprime a b → a ∣ (b*c) → a ∣ c` — Elements
    /// VII.30's engine; `euclid_lemma` is its corollary once `a` is prime.
    pub gauss_lemma: NameId,
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
}

/// Intern every name the integer development uses. Interning is not
/// declaration: this runs before anything is admitted, so the proof scripts can
/// name a law they have not yet reached.
fn intern_names(kernel: &mut Kernel, nat: NatPrelude) -> IntPrelude {
    let anon = kernel.anon();
    let z = kernel.name_str(anon, "Int");
    let child = |kernel: &mut Kernel, name: &str| kernel.name_str(z, name);
    let rat = kernel.name_str(anon, "Rat");
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
        add: child(kernel, "add"),
        mul: child(kernel, "mul"),
        neg: child(kernel, "neg"),
        sub: child(kernel, "sub"),
        zero: child(kernel, "zero"),
        one: child(kernel, "one"),
        le: child(kernel, "le"),
        lt: child(kernel, "lt"),
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
        add_lt_add_of_le_of_lt: child(kernel, "add_lt_add_of_le_of_lt"),
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
        pow: child(kernel, "pow"),
        pow_zero: child(kernel, "pow_zero"),
        pow_succ: child(kernel, "pow_succ"),
        pow_add: child(kernel, "pow_add"),
        pow_mul: child(kernel, "pow_mul"),
        prod_range: child(kernel, "prodRange"),
        prod_range_zero: child(kernel, "prodRange_zero"),
        prod_range_succ: child(kernel, "prodRange_succ"),
        prod_range_congr: child(kernel, "prodRange_congr"),
        prod_range_congr_lt: child(kernel, "prodRange_congr_lt"),
        prod_range_swap_adjacent: child(kernel, "prodRange_swap_adjacent"),
        prod_range_swap: child(kernel, "prodRange_swap"),
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
        ediv_emod_unique: child(kernel, "ediv_emod_unique"),
        dvd: child(kernel, "dvd"),
        dvd_refl: child(kernel, "dvd_refl"),
        dvd_trans: child(kernel, "dvd_trans"),
        dvd_add: child(kernel, "dvd_add"),
        dvd_mul_right: child(kernel, "dvd_mul_right"),
        dvd_mul_left: child(kernel, "dvd_mul_left"),
        emod_eq_zero_iff_dvd: child(kernel, "emod_eq_zero_iff_dvd"),
        mod_eq: child(kernel, "ModEq"),
        mod_eq_refl: child(kernel, "modEq_refl"),
        mod_eq_symm: child(kernel, "modEq_symm"),
        mod_eq_trans: child(kernel, "modEq_trans"),
        mod_eq_iff_dvd: child(kernel, "modEq_iff_dvd"),
        mod_eq_add_right: child(kernel, "modEq_add_right"),
        mod_eq_add_left: child(kernel, "modEq_add_left"),
        mod_eq_mul_left: child(kernel, "modEq_mul_left"),
        mod_eq_mul_right: child(kernel, "modEq_mul_right"),
        mod_eq_mul: child(kernel, "modEq_mul"),
        mod_eq_cancel: child(kernel, "modEq_cancel"),
        mod_eq_inverse_exists: child(kernel, "modEq_inverse_exists"),
        mod_eq_inverse_unique: child(kernel, "modEq_inverse_unique"),
        mod_eq_pow: child(kernel, "modEq_pow"),
        mod_eq_prod_range: child(kernel, "modEq_prodRange"),
        emod_neg: child(kernel, "emod_neg"),
        mod_eq_of_neg_modulus: child(kernel, "modEq_of_neg_modulus"),
        mod_eq_neg_modulus: child(kernel, "modEq_neg_modulus"),
        mod_eq_one: child(kernel, "modEq_one"),
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
        gcd_eq_gcd_ab: child(kernel, "gcd_eq_gcd_ab"),
        coprime: child(kernel, "Coprime"),
        coprime_of_bezout_one: child(kernel, "coprime_of_bezout_one"),
        gauss_lemma: child(kernel, "gauss_lemma"),
        euclid_lemma: child(kernel, "euclid_lemma"),
        euclid_infinitude: child(kernel, "euclid_infinitude"),
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
        factorial: child(kernel, "factorial"),
        factorial_zero: child(kernel, "factorial_zero"),
        factorial_succ: child(kernel, "factorial_succ"),
        self_inverse_mod_prime: child(kernel, "self_inverse_mod_prime"),
        factorial_pos: child(kernel, "factorial_pos"),
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
        order::declare_difference_lemmas(&mut d)?;
        order::declare_additive_order(&mut d)?;
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
        modeq::declare_modeq_add_right(&mut d)?;
        modeq::declare_modeq_add_left(&mut d)?;
        modeq::declare_modeq_mul_left(&mut d)?;
        modeq::declare_modeq_mul_right(&mut d)?;
        modeq::declare_modeq_mul(&mut d)?;
        modeq::declare_modeq_pow(&mut d)?;
        modeq_family::declare_emod_neg(&mut d)?;
        modeq_family::declare_modeq_of_neg_modulus(&mut d)?;
        modeq_family::declare_modeq_neg_modulus(&mut d)?;
        modeq_family::declare_modeq_one(&mut d)?;
        prod::declare_prod_range(&mut d)?;
        prod::declare_prod_range_equations(&mut d)?;
        prod::declare_prod_range_congr(&mut d)?;
        prod::declare_prod_range_congr_lt(&mut d)?;
        prod::declare_prod_range_swap_adjacent(&mut d)?;
        prod::declare_prod_range_swap(&mut d)?;
        prod::declare_modeq_prod_range(&mut d)?;
        wilson::declare_factorial(&mut d)?;
        wilson::declare_factorial_equations(&mut d)?;
        nat_abs::declare_nat_abs(&mut d)?;
        nat_abs::declare_nat_abs_lemmas(&mut d)?;
        nat_abs::declare_nat_abs_neg_of_nat(&mut d)?;
        nat_abs::declare_nat_abs_neg(&mut d)?;
        gcd::declare_gcd(&mut d)?;
        gcd::declare_gcd_comm(&mut d)?;
        gcd::declare_gcd_one_zero_right(&mut d)?;
        gcd::declare_nat_abs_mul(&mut d)?;
        nat_abs::declare_nat_abs_pow(&mut d)?;
        gcd::declare_dvd_of_nat_abs_dvd(&mut d)?;
        gcd::declare_nat_abs_dvd_nat_abs_of_dvd(&mut d)?;
        gcd::declare_gcd_dvd_left_right(&mut d)?;
        gcd::declare_dvd_gcd(&mut d)?;
        gcd::declare_gcd_eq_gcd_ab(&mut d)?;
        gcd::declare_coprime(&mut d)?;
        gcd::declare_coprime_of_bezout_one(&mut d)?;
        gcd::declare_gauss_lemma(&mut d)?;
        modeq::declare_modeq_cancel(&mut d)?;
        gcd::declare_modeq_inverse_exists(&mut d)?;
        modinv::declare_modeq_inverse_unique(&mut d)?;
        gcd::declare_euclid_lemma(&mut d)?;
        gcd::declare_euclid_infinitude(&mut d)?;
        wilson::declare_self_inverse_mod_prime(&mut d)?;
        wilson::declare_factorial_pos(&mut d)?;
        crt::declare_crt_exists(&mut d)?;
        crt::declare_crt_unique(&mut d)?;
        rat::declare_rat(&mut d)?;
        rat::declare_normalize(&mut d)?;
        rat::declare_arithmetic(&mut d)?;
        rat::declare_more_arithmetic(&mut d)?;
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
