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
mod statements;

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
/// construction below *could* prove, and does not yet.
fn declare_remaining_axioms(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let laws: [AssertedLaw; 6] = [
        (p.add_assoc, 3, statements::add_assoc),
        (p.mul_assoc, 3, statements::mul_assoc),
        (p.left_distrib, 3, statements::left_distrib),
        (p.add_le_add, 4, statements::add_le_add),
        (
            p.add_lt_add_of_le_of_lt,
            4,
            statements::add_lt_add_of_le_of_lt,
        ),
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
        order::declare_order_theorems(&mut d)?;
        algebra::declare_algebra_theorems(&mut d)?;
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
