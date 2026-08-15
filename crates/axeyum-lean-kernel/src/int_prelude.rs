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
//! of `ℕ × ℕ` is the other textbook route, and in *this* kernel it is strictly
//! worse: `Quot`/`Quot.sound` are admitted as `Declaration::Quotient`, i.e. as
//! trusted declarations, so every integer theorem's
//! [`axiom_footprint`](crate::Kernel::axiom_footprint) would name `Quot.sound`
//! forever. With `ofNat`/`negSucc` each integer has exactly one representative,
//! `Eq Int` is ordinary propositional equality, and a derived law's footprint
//! is genuinely empty.
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

use crate::expr::ExprId;
use crate::name::NameId;
use crate::nat_prelude::{NatPrelude, build_nat_prelude};
use crate::{Kernel, KernelError, LogicPrelude, PreludeKey, PreludeValue};

mod algebra;
mod decide;
mod defs;
mod ops;
mod order;
mod sign;
mod statements;
mod sub_nat_nat;

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
    /// `mul_zero : ∀ (a : Int), Eq Int (mul a zero) zero`.
    pub mul_zero: NameId,
    /// `left_distrib :
    /// ∀ (a b c : Int), Eq Int (mul a (add b c)) (add (mul a b) (mul a c))`.
    pub left_distrib: NameId,
    /// `mul_nonneg : ∀ (a b : Int), le zero a → le zero b → le zero (mul a b)`.
    pub mul_nonneg: NameId,

    // --- discreteness and decision laws --------------------------------------
    /// `no_int_between : ∀ (x : Int), Not (And (lt zero x) (lt x one))`.
    pub no_int_between: NameId,
    /// `le_total : ∀ (a b : Int), Or (le a b) (le b a)`.
    pub le_total: NameId,
    /// `lt_of_le_of_ne :
    /// ∀ (a b : Int), le a b → Not (Eq Int a b) → lt a b`.
    pub lt_of_le_of_ne: NameId,
    /// `euclidean_decomposition : ∀ t k, 0 < k → ∃ q r, t = k*q+r ∧ 0 ≤ r ∧ r < k`.
    pub euclidean_decomposition: NameId,
    /// `eq_em : ∀ (a b : Int), Or (Eq Int a b) (Not (Eq Int a b))`.
    pub eq_em: NameId,
}

/// Intern every name the integer development uses. Interning is not
/// declaration: this runs before anything is admitted, so the proof scripts can
/// name a law they have not yet reached.
fn intern_names(kernel: &mut Kernel, nat: NatPrelude) -> IntPrelude {
    let anon = kernel.anon();
    let z = kernel.name_str(anon, "Int");
    let child = |kernel: &mut Kernel, name: &str| kernel.name_str(z, name);
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
        add_lt_add_of_le_of_lt: child(kernel, "add_lt_add_of_le_of_lt"),
        mul_le_mul_of_nonneg_left: child(kernel, "mul_le_mul_of_nonneg_left"),
        zero_lt_one: child(kernel, "zero_lt_one"),
        mul_comm: child(kernel, "mul_comm"),
        mul_assoc: child(kernel, "mul_assoc"),
        mul_one: child(kernel, "mul_one"),
        mul_zero: child(kernel, "mul_zero"),
        left_distrib: child(kernel, "left_distrib"),
        mul_nonneg: child(kernel, "mul_nonneg"),
        no_int_between: child(kernel, "no_int_between"),
        le_total: child(kernel, "le_total"),
        lt_of_le_of_ne: child(kernel, "lt_of_le_of_ne"),
        euclidean_decomposition: child(kernel, "euclidean_decomposition"),
        eq_em: child(kernel, "eq_em"),
    }
}

/// One asserted law: its name, the arity of its `Int` telescope, and its
/// statement builder. Kept as data so the undischarged remainder is a *list*
/// that shrinks visibly as laws move to [`order`] and [`algebra`].
type AssertedLaw = (NameId, usize, fn(&mut IntDev<'_>, &[ExprId]) -> ExprId);

/// Assert the laws this development has not derived.
///
/// Each entry here is a standing debt: it is a true fact about `ℤ` that the
/// construction below *could* prove, and does not yet. One is left, and it is
/// the only one that is not a ring or order law: `euclidean_decomposition`
/// asserts the *existence* of a quotient and remainder, so discharging it needs
/// integer division as a definition, not another rewriting lemma.
fn declare_remaining_axioms(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let laws: [AssertedLaw; 1] = [
        // Kept last: `prelude_composition`'s rollback test conflicts on this
        // name precisely because it is the final member admitted.
        (
            p.euclidean_decomposition,
            2,
            statements::euclidean_decomposition,
        ),
    ];
    for (name, arity, statement) in laws {
        d.int_axiom(name, arity, &statement)?;
    }
    Ok(())
}

/// Build the integer prelude: `ℤ` constructed over the proved `ℕ` development,
/// plus the laws not yet derived.
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
        sign::declare_mul_assoc(&mut d)?;
        sub_nat_nat::declare_mul_lemmas(&mut d)?;
        algebra::declare_left_distrib(&mut d)?;
        order::declare_difference_lemmas(&mut d)?;
        order::declare_additive_order(&mut d)?;
        decide::declare_decidable_equality(&mut d)?;
        algebra::declare_ordered_multiplication(&mut d)?;
        declare_remaining_axioms(&mut d)?;
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
