//! **ℝ, constructed**: a Bishop setoid of regular sequences of rationals over
//! the proved `ℚ`, with equality carried by a *defined* relation rather than by
//! `Eq`, and costing **zero** trusted declarations.
//!
//! This is ADR-0512
//! (`docs/research/09-decisions/adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md`)
//! phase R1, and it is what `examples/creal_shape_probe.rs` measured the shape
//! of before `ℚ` had an order. The probe admitted
//! `CReal.Of (reg : (Nat → Rat) → Prop)` — the carrier *parametric* in its
//! regularity predicate, because `Rat.le` did not exist. It does now, so the
//! predicate is a definition and the carrier is concrete.
//!
//! ## Why a setoid, in one line
//!
//! ADR-0456 priced the two textbook routes and found both closed here: a Cauchy
//! **quotient** needs `Quot.sound`, which this kernel's four-declaration
//! quotient package does not contain, and **Dedekind cuts** need `funext` and
//! `propext`, neither of which exists. The missing option was that equality
//! need not be `Eq`. `CReal.Equiv` is a `Prop`-valued definition, so the whole
//! construction is ordinary definitions and theorems.
//!
//! `Eq CReal` is **not** the equality of real numbers, and nothing here pretends
//! it is. `0.999… ` and `1` are distinct `CReal`s and `CReal.Equiv`-equal, which
//! is the correct and intended state of affairs.
//!
//! ## The three shapes this module is built out of
//!
//! - **`|a| ≤ b` is a pair.** [`Within`](CRealPrelude::within) is
//!   `−b ≤ a ∧ a ≤ b`, so `Rat.abs` is never needed — no sign case split, no
//!   congruence lemma, no monotonicity theory.
//! - **Every bound is one `Rat.natDivSucc`.** `1/(m+1)`, `2/(n+1)` and `6/(j+1)`
//!   are the same construction at different numerators, which is what lets the
//!   six-term estimate in [`Equiv.trans`](CRealPrelude::equiv_trans) fuse.
//! - **Regularity is a fixed modulus, not an existential.** Bishop's
//!   `|f m − f n| ≤ 1/(m+1) + 1/(n+1)` keeps the representative a plain
//!   function: the modulus never has to be extracted, and completeness will
//!   later be provable without countable choice. That is the trap a bare-Cauchy
//!   development falls into and the reason the HoTT book reaches for a higher
//!   inductive type.
//!
//! ## What transitivity costs, and where it is paid
//!
//! Chaining two closeness hypotheses directly gives `|x_n − z_n| ≤ 4/(n+1)`,
//! which is not the `≤ 2/(n+1)` the relation asks for, and no rearrangement
//! fixes that. Bishop compares at an arbitrary third index `j`:
//!
//! ```text
//! |x_n − z_n| ≤ |x_n − x_j| + |x_j − y_j| + |y_j − z_j| + |z_j − z_n|
//!             ≤ (1/(n+1) + 1/(j+1)) + 2/(j+1) + 2/(j+1) + (1/(j+1) + 1/(n+1))
//!              = 2/(n+1) + 6/(j+1)
//! ```
//!
//! and the `6/(j+1)` is discharged by
//! [`Rat.le_of_le_add_natDivSucc`](crate::RatPrelude::le_of_le_add_natDivSucc)
//! — the **Archimedean property of ℚ**, a statement about rationals that this
//! module only consumes. That is the price of the fixed modulus, and it is paid
//! twice: here, and in [`lt_irrefl`](CRealPrelude::lt_irrefl).
//!
//! ## The strict order quantifies over the gap, not over an index
//!
//! [`CReal.lt`](CRealPrelude::lt) is `∃ (q : Rat), 0 < q ∧ x + q ≤ y`. The two
//! shapes a textbook suggests are both closed here:
//!
//! - `lt x y := Not (le y x)` makes [`le_of_lt`](CRealPrelude::le_of_lt)
//!   non-constructive, and there is no `le_total` over ℝ to recover it from —
//!   `Rat.le_total` holds for ℚ and does not lift.
//! - `∃ (n : Nat), y_n − x_n > 2/(n+1)`, Bishop's own, does not give
//!   [`lt_trans`](CRealPrelude::lt_trans) as written: composing two witnesses
//!   needs a *new* index, and the two regularity round trips that reach it
//!   consume precisely the margin the hypotheses supply. Chaining at a third
//!   index `k` leaves `z_k − x_k > −2/(k+1) − 1/(m+1) − 1/(n+1)`, which is
//!   negative for every choice, so closing it needs a quantitative gap lemma —
//!   the same thing the fixed modulus does not supply for `mul`.
//!
//! Carrying the *rational gap* removes the recomputation entirely: `lt_trans`
//! hands `q₁` through untouched and reads the second hypothesis only through
//! `le_of_lt`. The one analytic step left is
//! [`le_add_of_nonneg`](CRealPrelude::le_add_of_nonneg), and it is analytic
//! only because of the index shift — it closes on [`shifted_bound_le`], the
//! same inequality `add_zero` and `add_assoc` reduce to.

// Proof scripts are long, straight-line term constructions with short
// mathematical names, exactly as in `rat_prelude`.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use crate::BinderInfo;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::{rsub, rsum, rsum_append, rsum_perm};
use crate::rat_prelude::ops::{
    radd, rat_eq_rewrite, rat_ty, rchain, rcongr, rle, rlt, rneg, rone, rrefl, rsymm, rzero,
};
use crate::rat_prelude::{RatPrelude, build_rat_prelude};
use crate::{Kernel, KernelError, PreludeKey, PreludeValue};

/// Delta heights for the real definitions: above every `Rat` definition.
const LEAF_HEIGHT: u16 = 40;
/// Height for a definition that calls a leaf one.
const DERIVED_HEIGHT: u16 = 41;

/// The interned names produced by [`build_creal_prelude`]: the carrier, its
/// constructor and recursor, the two projections, the setoid relation, and its
/// three equivalence laws — plus the embedded [`RatPrelude`] the whole thing is
/// constructed over.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CRealPrelude {
    /// The rational development `CReal` is constructed over. Its axiom
    /// footprint is empty, which is what makes every law below empty too.
    pub rat: RatPrelude,

    /// `CReal.Within : Rat → Rat → Prop` — `Within r q := −q ≤ r ∧ r ≤ q`.
    ///
    /// ADR-0512's encoding of `|r| ≤ q`, chosen so that `Rat.abs` never has to
    /// exist. Every bound in this module is stated through it.
    pub within: NameId,
    /// `CReal.Regular : (Nat → Rat) → Prop` — Bishop regularity with the
    /// **fixed** modulus `|f m − f n| ≤ 1/(m+1) + 1/(n+1)`.
    pub regular_pred: NameId,
    /// `CReal : Type` — a one-constructor inductive. **Not** a quotient: this
    /// kernel has no `Quot.sound` (ADR-0456), and does not need one.
    pub creal: NameId,
    /// `CReal.mk : (f : Nat → Rat) → CReal.Regular f → CReal`.
    pub mk: NameId,
    /// `CReal.rec` — the kernel-generated recursor.
    pub rec: NameId,
    /// `CReal.seq : CReal → Nat → Rat` — the representative, by **large
    /// elimination** out of a `Type`-valued inductive with a `Prop` field.
    pub seq: NameId,
    /// `CReal.regular : ∀ x, CReal.Regular (CReal.seq x)` — the regularity
    /// field, projected.
    pub regular: NameId,
    /// `CReal.Equiv : CReal → CReal → Prop` —
    /// `∀ n, Within (seq x n − seq y n) (2/(n+1))`.
    ///
    /// **This, and not `Eq CReal`, is the equality of real numbers.**
    pub equiv: NameId,
    /// `CReal.Equiv.refl : ∀ x, CReal.Equiv x x`.
    pub equiv_refl: NameId,
    /// `CReal.Equiv.symm : ∀ x y, CReal.Equiv x y → CReal.Equiv y x`.
    pub equiv_symm: NameId,
    /// `CReal.Equiv.trans : ∀ x y z, CReal.Equiv x y → CReal.Equiv y z → CReal.Equiv x z`.
    ///
    /// The one proof in the construction that is not routine — see the module
    /// documentation. It is the only consumer of the Archimedean property.
    pub equiv_trans: NameId,

    // --- the carrier is inhabited, and `Equiv` discriminates ------------------
    /// `CReal.ofRat : Rat → CReal` — the embedding `ℚ ↪ ℝ`, the constant
    /// sequence.
    ///
    /// It is also the **non-vacuity** witness. Everything above is a statement
    /// about the inhabitants of `CReal`, so if `CReal.Regular` had no solutions
    /// the carrier would be empty and `refl`, `symm` and `trans` would all be
    /// true and worthless — and an empty axiom footprint would not notice.
    pub of_rat: NameId,
    /// `CReal.Equiv.not_zero_one : Not (CReal.Equiv (ofRat Rat.zero) (ofRat Rat.one))`.
    ///
    /// The **discrimination** witness. `Equiv` being an equivalence relation is
    /// worth nothing if `Equiv` is the total relation; this exhibits two
    /// `CReal`s it separates, and it separates them *by computation* — the
    /// witness index is `3`, and `−1/2 ≤ −1` reduces to `Nat.le 1 0`.
    pub not_zero_one: NameId,

    // --- the additive structure (ADR-0512 phase R2, partial) -----------------
    /// `CReal.zero : CReal` — `ofRat Rat.zero`.
    pub zero: NameId,
    /// `CReal.one : CReal` — `ofRat Rat.one`.
    pub one: NameId,
    /// `CReal.Equiv.of_pointwise : ∀ x y, (∀ n, Eq Rat (seq x n) (seq y n)) → Equiv x y`.
    ///
    /// The bridge from `Eq` to `Equiv`, and the reason the *pointwise* laws
    /// below are cheap: an operation whose two sides agree at every index is
    /// `Equiv`-equal without any analytic argument at all. It is one-way, and
    /// deliberately: the converse is false, which is the whole reason `CReal`
    /// is a setoid.
    pub equiv_of_pointwise: NameId,
    /// `CReal.neg : CReal → CReal` — pointwise negation. **No index shift**:
    /// negation does not degrade the modulus, which is why it lands before
    /// `add` does.
    pub neg: NameId,
    /// `CReal.neg_congr : ∀ x y, Equiv x y → Equiv (neg x) (neg y)` — the first
    /// of the setoid's congruence obligations, which ADR-0512 counts as the
    /// construction's real tax.
    pub neg_congr: NameId,
    /// `CReal.neg_le_neg : ∀ x y, le x y → le (neg y) (neg x)`.
    ///
    /// Negation reverses `le`. Bishop's `le` is already one-sided
    /// (`∀ n, seq x n − seq y n ≤ 2/(n+1)`), so this is a single
    /// `Rat.sub_neg_sub` rewrite at each index — no shift, matching `neg`'s
    /// own definition. One of the two order/negation facts a cotransitivity
    /// argument over a negative threshold needs; the other is
    /// [`Self::neg_mul_neg`].
    pub neg_le_neg: NameId,
    /// `CReal.add : CReal → CReal → CReal`, with **Bishop's index shift**:
    /// `(x + y)_n := x_{2n+1} + y_{2n+1}`.
    ///
    /// The shift is not decoration. Adding two regular sequences doubles the
    /// error, so the naive pointwise sum is *not* regular; sampling at `2n+1`
    /// halves each modulus first, and
    /// [`Rat.natDivSucc_halve`](crate::RatPrelude::nat_div_succ_halve) is the
    /// identity that cashes the trade.
    pub add: NameId,
    /// `CReal.add_congr : ∀ x x' y y', Equiv x x' → Equiv y y' →
    /// Equiv (add x y) (add x' y')` — the second congruence obligation.
    pub add_congr: NameId,
    /// `CReal.add_comm : ∀ x y, Equiv (add x y) (add y x)` — one of the 22, in
    /// `Equiv` form. Both sides sample at the same index, so it is *pointwise*
    /// and costs one `Rat.add_comm`.
    pub add_comm: NameId,
    /// `CReal.add_neg : ∀ x, Equiv (add x (neg x)) zero` — one of the 22, in
    /// `Equiv` form, and pointwise for the same reason.
    pub add_neg: NameId,
    /// `CReal.add_zero : ∀ x, Equiv (add x zero) x` — one of the 22, and the
    /// first that is **not** pointwise: `add x zero` samples `x` at `2n+1`
    /// where `x` samples it at `n`, so the two sides are not equal at any
    /// index and `Equiv.of_pointwise` does not apply. Regularity closes the
    /// gap, and the slack is paid by `shifted_bound_le`.
    pub add_zero: NameId,
    /// `CReal.le : CReal → CReal → Prop` —
    /// `le x y := ∀ n, seq x n − seq y n ≤ 2/(n+1)`.
    ///
    /// Bishop's order, and the **one-sided** reading of `Equiv`: `Equiv x y`
    /// is exactly `le x y ∧ le y x` unfolded. That is not a coincidence to be
    /// exploited later, it is why the order laws cost so little here — every
    /// estimate `Equiv` needed is already one-sided inside, and the two-sided
    /// version was the expensive packaging.
    ///
    /// **`le` is not decidable and no totality law is stated.** `le_or_lt`
    /// holds for `ℚ` and does not lift: `∀ x y, le x y ∨ le y x` over the reals
    /// is not constructively provable, and nothing below assumes it.
    pub le: NameId,
    /// `CReal.le_refl : ∀ x, le x x` — one of the 22, and verbatim: it
    /// mentions no `Eq`, so unlike the additive laws it does not have to be
    /// restated over `Equiv`.
    pub le_refl: NameId,
    /// `CReal.le_trans : ∀ x y z, le x y → le y z → le x z` — one of the 22,
    /// verbatim, and the **upper half of `Equiv.trans`**: the same four-term
    /// estimate at an arbitrary index `j`, the same
    /// `telescope_four`/`six_term_bound`, the same Archimedean lemma —
    /// with `Rat.add_le_add` in place of `Rat.bounds_add` and no negated
    /// branch at all.
    pub le_trans: NameId,
    /// `CReal.add_le_add : ∀ x x' y y', le x x' → le y y' →
    /// le (add x y) (add x' y')` — one of the 22, verbatim. Exact, like
    /// `add_congr`: two `2/(2n+2)` bounds sum to `2/(n+1)` with no slack.
    pub add_le_add: NameId,
    /// `CReal.le_of_equiv : ∀ x y, Equiv x y → le x y`.
    ///
    /// Half of the coherence between the order and the setoid's equality, and
    /// it is a projection: `Equiv` *is* the two-sided bound whose upper half is
    /// `le`.
    pub le_of_equiv: NameId,
    /// `CReal.equiv_of_le_le : ∀ x y, le x y → le y x → Equiv x y`.
    ///
    /// The other half — **antisymmetry up to `Equiv`** — and the reason the
    /// three order laws are laws about *this* order rather than about some
    /// coarser relation that happens to satisfy them. A `le` weakened to
    /// `≤ 100/(n+1)` would still be reflexive, transitive and additive; it
    /// would not close this.
    pub equiv_of_le_le: NameId,
    /// `CReal.not_le_one_zero : Not (le one zero)`.
    ///
    /// The **discrimination** witness for the order, and the reason the three
    /// laws above are worth anything: `le_refl`, `le_trans` and `add_le_add`
    /// all hold, footprint-free, of the relation that relates everything. This
    /// exhibits a pair `le` separates, by computation — at index `3` the claim
    /// is `1 ≤ 1/2`, which unfolds through `Int.le` to `Nat.le 2 1`.
    pub not_le_one_zero: NameId,
    /// `CReal.add_assoc : ∀ x y z, Equiv (add (add x y) z) (add x (add y z))`
    /// — one of the 22, and the analytic one: `(x+y)+z` samples `x` at
    /// `2(2n+1)+1` while `x+(y+z)` samples it at `2n+1`, and `z` the other way
    /// round. `y` is sampled at the same index on both sides and cancels, so
    /// the whole difference is `(x_M − x_N) + (z_N − z_M)` — two regularity
    /// bounds, and then the *same* inequality `add_zero` needs.
    pub add_assoc: NameId,
    /// `CReal.ofRat_add : ∀ a b, Equiv (add (ofRat a) (ofRat b)) (ofRat (Rat.add a b))`
    /// — the additive counterpart of [`Self::of_rat_mul`]. Both sides sample
    /// the same closed rational at every index, because `ofRat` is a constant
    /// sequence and `add`'s index shift never touches a constant, so the
    /// pointwise proof is `Eq.refl`, exactly as `of_rat_mul`'s is.
    pub of_rat_add: NameId,
    /// `CReal.ofRat_neg : ∀ a, Equiv (neg (ofRat a)) (ofRat (Rat.neg a))`.
    ///
    /// `CReal.neg` takes **no** index shift, so this is the simplest of the
    /// three: both sides reduce to `Rat.neg a` at every index with no shift to
    /// reconcile at all.
    pub of_rat_neg: NameId,
    /// `CReal.ofRat_sub : ∀ a b,
    /// Equiv (add (ofRat a) (neg (ofRat b))) (ofRat (Rat.sub a b))`.
    ///
    /// `CReal` has no `sub` operator of its own — every other module states
    /// subtraction as `add x (neg y)`, which is what `Rat.sub` itself unfolds
    /// to — so this is stated over that combination rather than inventing one.
    pub of_rat_sub: NameId,

    // --- the strict order (ADR-0512 phase R2, continued) ---------------------
    /// `CReal.le_add_of_nonneg : ∀ x q, Rat.le Rat.zero q →
    /// CReal.le x (CReal.add x (CReal.ofRat q))`.
    ///
    /// The one analytic step the strict order needs, and it is analytic only
    /// because of Bishop's index shift: even at `q = 0` the two sides sample
    /// `x` at different indices. Same slack, same `shifted_bound_le`.
    pub le_add_of_nonneg: NameId,
    /// `CReal.lt : CReal → CReal → Prop` —
    /// `lt x y := ∃ (q : Rat), Rat.lt Rat.zero q ∧ le (add x (ofRat q)) y`.
    ///
    /// **The gap is a rational and it is carried, not recomputed.** Two shapes
    /// were tried and closed: `lt := Not (le y x)` makes
    /// [`le_of_lt`](Self::le_of_lt) non-constructive with no `le_total` over ℝ
    /// to recover it from (`Rat.le_total` holds for ℚ and does not lift), and
    /// `∃ n, y_n − x_n > 2/(n+1)` does not give
    /// [`lt_trans`](Self::lt_trans) — composing two such witnesses needs a new
    /// index, and the two regularity round trips reaching it consume exactly
    /// the margin the hypotheses supply. Quantifying over the *gap* instead
    /// makes transitivity carry `q₁` through untouched.
    pub lt: NameId,
    /// `CReal.lt_irrefl : ∀ x, Not (lt x x)` — one of the 22, verbatim, and the
    /// **discrimination** witness for `lt` together with
    /// [`zero_lt_one`](Self::zero_lt_one).
    pub lt_irrefl: NameId,
    /// `CReal.lt_trans : ∀ x y z, lt x y → lt y z → lt x z` — one of the 22,
    /// verbatim.
    pub lt_trans: NameId,
    /// `CReal.lt_of_lt_of_le : ∀ x y z, lt x y → le y z → lt x z` — one of the
    /// 22, verbatim.
    pub lt_of_lt_of_le: NameId,
    /// `CReal.lt_of_le_of_lt : ∀ x y z, le x y → lt y z → lt x z` — one of the
    /// 22, verbatim.
    pub lt_of_le_of_lt: NameId,
    /// `CReal.le_of_lt : ∀ x y, lt x y → le x y` — one of the 22, verbatim.
    pub le_of_lt: NameId,
    /// `CReal.zero_lt_one : lt zero one` — one of the 22, verbatim, and the
    /// **non-vacuity** witness for `lt`: the other six strict-order laws all
    /// consume a `lt` and so hold, footprint-free, of the empty relation.
    pub zero_lt_one: NameId,
    /// `CReal.add_lt_add_of_le_of_lt : ∀ x y c e, le x y → lt c e →
    /// lt (add x c) (add y e)` — one of the 22, verbatim.
    pub add_lt_add_of_le_of_lt: NameId,
    /// `CReal.le_congr : ∀ a b c e, Equiv a b → Equiv c e → le a c → le b e`.
    ///
    /// Not one of the 22 — one of the nine equality-slot binders the setoid
    /// ring telescope takes (ADR-0512 phase R3).
    pub le_congr: NameId,
    /// `CReal.lt_congr : ∀ a b c e, Equiv a b → Equiv c e → lt a c → lt b e`.
    ///
    /// The other relation congruence of the equality slot.
    pub lt_congr: NameId,

    // --- the product (ADR-0512 phase R2, continued) --------------------------
    /// `CReal.bound : CReal → Nat` — `Int.natAbs (Rat.num (seq x 0)) + 1`.
    ///
    /// The **canonical magnitude**, and the one thing `CReal.mul` needs that
    /// `CReal.add` did not. It is a projection, not a search: with ADR-0512's
    /// *fixed* modulus, regularity at index `0` bounds every sample by
    /// `|x_0| + 2` outright, so nothing has to be extracted from an
    /// existential — which is exactly what a `CauSeq` development has to do.
    pub bound: NameId,
    /// `CReal.bound_within : ∀ x m,
    /// Within (seq x m) (Rat.natDivSucc (CReal.bound x + 1) 0)`.
    pub bound_within: NameId,
    /// `CReal.mulShift : CReal → CReal → Nat` —
    /// `bound x + bound y + 1`, the `c` of the sampling index `(c+1)·n + c`.
    ///
    /// Written as a successor so that `c + 1` **is** `(bound x + 1) +
    /// (bound y + 1)`, the sum of the two canonical magnitudes, with no
    /// ℕ-subtraction anywhere.
    pub mul_shift: NameId,
    /// `CReal.mul : CReal → CReal → CReal` — `(x·y)_n := x_j · y_j` at
    /// `j = (c+1)·n + c`.
    ///
    /// The estimate closes **exactly**: the four terms of the product bound
    /// fuse to `(Kx+Ky)/(A+1) + (Kx+Ky)/(B+1)`, and `Rat.natDivSucc_scale`
    /// reads each as the regularity bound on the nose. No slack, no weakening,
    /// and `Rat.natDivSucc` still never needed antitone in its index.
    pub mul: NameId,
    /// `CReal.equiv_of_bounded : ∀ x y (K : Nat),
    /// (∀ n, Within (seq x n − seq y n) (Rat.natDivSucc K n)) → Equiv x y`.
    ///
    /// **`Equiv` only needs the difference to be `O(1/n)`; the constant is
    /// free.** It is `Equiv.trans`'s argument with one term deleted, closed by
    /// the Archimedean property of ℚ — whose numerator is a `Nat` *parameter*,
    /// so a symbolic constant built out of the factors' `CReal.bound`s is as
    /// acceptable as a literal. Every law whose two sides sample at *different*
    /// indices goes through this.
    pub equiv_of_bounded: NameId,
    /// `CReal.mul_congr : ∀ x x' y y', Equiv x x' → Equiv y y' →
    /// Equiv (mul x y) (mul x' y')` — the **fifth congruence obligation**, not
    /// one of the 22, and a prerequisite for ADR-0512 phase R4.
    pub mul_congr: NameId,
    /// `CReal.ofRat_mul : ∀ q r, Equiv (mul (ofRat q) (ofRat r)) (ofRat (q·r))`
    /// — `CReal.mul` restricted to the embedded `ℚ` **is** `Rat.mul`.
    ///
    /// Not one of the 22, and the reason the ones that are mean anything: it
    /// pins the operation rather than asserting a property of it. Every
    /// degenerate product a footprint check would wave through — the constant
    /// `zero`, either projection, `add` in disguise — fails it.
    pub of_rat_mul: NameId,
    /// `CReal.mul_comm : ∀ x y, Equiv (mul x y) (mul y x)` — one of the 22, in
    /// `Equiv` form, and *pointwise*: the two shifts differ only by
    /// `Nat.add_comm` inside `CReal.mulShift`.
    pub mul_comm: NameId,
    /// `CReal.mul_one : ∀ x, Equiv (mul x one) x` — one of the 22, and the
    /// first product law that is **not** pointwise.
    pub mul_one: NameId,
    /// `CReal.mul_zero : ∀ x, Equiv (mul x zero) zero` — one of the 22, in
    /// `Equiv` form, and pointwise: `Rat.mul_zero` at every index.
    pub mul_zero: NameId,
    /// `CReal.mul_assoc : ∀ x y z,
    /// Equiv (mul (mul x y) z) (mul x (mul y z))` — one of the 22, in `Equiv`
    /// form, and the only law with a **nested** sampling index on each side.
    pub mul_assoc: NameId,
    /// `CReal.mul_le_mul_of_nonneg_left : ∀ x y z, le zero x → le y z →
    /// le (mul x y) (mul x z)` — one of the 22, **verbatim**, and the only one
    /// of the eight that is not an estimate: it is
    /// [`Self::left_distrib`] plus [`Self::mul_nonneg`] plus
    /// [`Self::mul_congr`].
    pub mul_le_mul_of_nonneg_left: NameId,
    /// `CReal.left_distrib : ∀ x y z,
    /// Equiv (mul x (add y z)) (add (mul x y) (mul x z))` — one of the 22, in
    /// `Equiv` form, and the first law whose two sides agree at **no** index
    /// and whose sampling shifts are not even equal as naturals.
    pub left_distrib: NameId,
    /// `CReal.mul_nonneg : ∀ x y, le zero x → le zero y → le zero (mul x y)` —
    /// one of the 22, verbatim.
    ///
    /// `0 ≤ x` over the reals does **not** say any sample of `x` is
    /// non-negative — only that each sits above `−2/(j+1)` — so the product's
    /// lower bound trades that residue against the other factor's canonical
    /// magnitude, and `2/(j+1) · (c+1)/1` fuses back to exactly `2/(n+1)`.
    pub mul_nonneg: NameId,
    /// `CReal.sq_nonneg : ∀ x, le zero (mul x x)` — one of the 22, verbatim,
    /// and free: `x_j·x_j ≥ 0` already holds in `ℚ`.
    pub sq_nonneg: NameId,
    /// `CReal.neg_mul_neg : ∀ x, Equiv (mul (neg x) (neg x)) (mul x x)`.
    ///
    /// **Not pointwise**, unlike [`Self::mul_comm`]/[`Self::mul_zero`]:
    /// `CReal.bound` reads `Int.natAbs (Rat.num (seq x 0))`, and negating the
    /// representative negates that numerator, so `mulShift (neg x) (neg x)`
    /// and `mulShift x x` are not the *same* natural literal — they are
    /// **provably equal** (`Int.natAbs_neg`), which is exactly what lets both
    /// products sample at a *value-equal* index and this be `Equiv`, not just
    /// an estimate. The other of the two facts a negative-threshold
    /// cotransitivity argument needs; see [`Self::neg_le_neg`].
    pub neg_mul_neg: NameId,
    /// `CReal.not_equiv_mul_one_one_zero : Not (Equiv (mul one one) zero)`.
    ///
    /// The **discrimination** witness for the product. `mul_zero`, `mul_comm`
    /// and `sq_nonneg` all hold, footprint-free, of `fun _ _ => zero`; this
    /// refuses that product by computation, through [`Self::of_rat_mul`].
    pub not_equiv_mul_one_one_zero: NameId,

    // --- apartness, and the obstruction to a total inverse (ADR-0510) --------
    /// `CReal.Apart : CReal → CReal → Prop` — `Apart x y := lt x y ∨ lt y x`.
    ///
    /// **Bishop's apartness, verbatim.** [`CReal.lt`](Self::lt) already carries
    /// the separation as a rational gap, so the disjunction is the whole
    /// definition and every law below is a rearrangement of the strict order.
    ///
    /// `Apart x y` is *strictly stronger* than `Not (Equiv x y)`
    /// ([`Self::not_equiv_of_apart`] is the one direction that holds), and it
    /// is the domain the multiplicative inverse has to be stated over. The
    /// converse is Markov's principle and is neither proved nor assumed here.
    pub apart: NameId,
    /// `CReal.apart_symm : ∀ x y, Apart x y → Apart y x`.
    pub apart_symm: NameId,
    /// `CReal.apart_irrefl : ∀ x, Not (Apart x x)`.
    pub apart_irrefl: NameId,
    /// `CReal.apart_congr : ∀ a b c e, Equiv a b → Equiv c e → Apart a c →
    /// Apart b e` — the setoid congruence for apartness.
    pub apart_congr: NameId,
    /// `CReal.not_equiv_of_apart : ∀ x y, Apart x y → Not (Equiv x y)`.
    ///
    /// One-way on purpose: the converse is Markov's principle.
    pub not_equiv_of_apart: NameId,
    /// `CReal.apart_zero_one : Apart CReal.zero CReal.one` — the **non-vacuity**
    /// witness. The three laws above all hold, footprint-free, of the relation
    /// that separates nothing.
    pub apart_zero_one: NameId,
    /// `CReal.no_total_inverse : ∀ (f : CReal → CReal),
    /// Not (∀ x, Equiv (mul x (f x)) one)`.
    ///
    /// **The missing structure, as a theorem.** No function on all of `CReal`
    /// is a multiplicative inverse — evaluate at `zero` — so "the inverse is
    /// partial" is a proved obstruction here rather than a scoping note. The
    /// field analogue of `Complex.no_compatible_order`.
    pub no_total_inverse: NameId,
    /// `CReal.ofRat_le : ∀ a b, Rat.le a b → CReal.le (ofRat a) (ofRat b)` —
    /// the embedding `ℚ ↪ ℝ` is monotone.
    pub of_rat_le: NameId,
    /// `CReal.PosBound : CReal → Nat → Prop` —
    /// `PosBound x k := le (ofRat (Rat.natDivSucc 1 k)) x`.
    ///
    /// **The domain of the multiplicative inverse**, with its modulus carried
    /// as data. `0 < x` is a `Prop` and cannot be eliminated into `Type`;
    /// `PosBound x k` is a `Prop` *about a `Nat` the caller supplies*, and a
    /// function may take it as an argument and still return a `CReal`, because
    /// the proof is only ever used to discharge a `Prop`-valued field.
    pub pos_bound: NameId,
    /// `CReal.pos_of_pos_bound : ∀ x k, PosBound x k → lt zero x`.
    pub pos_of_pos_bound: NameId,
    /// `CReal.pos_bound_of_lt : ∀ x, lt zero x → ∃ (k : Nat), PosBound x k`.
    ///
    /// With [`Self::pos_of_pos_bound`] this says `0 < x` and
    /// `∃ k, 1/(k+1) ≤ x` are the **same proposition** — the separating modulus
    /// always exists — while `Exists` is a `Prop`, so the `k` can never be
    /// extracted into a `CReal`. That pair is the precise statement of why the
    /// inverse takes its modulus as an argument.
    pub pos_bound_of_lt: NameId,
    /// `CReal.ofRat_pos : ∀ g, Rat.lt Rat.zero g → lt zero (ofRat g)`.
    pub of_rat_pos: NameId,
    /// `CReal.mul_pos : ∀ x y, lt zero x → lt zero y → lt zero (mul x y)`.
    ///
    /// **Not one of the 22.** They give `mul_nonneg`, of which the zero product
    /// is a model; strictness is what a field needs, and over ℚ it goes through
    /// [`Rat.inv_pos`](crate::RatPrelude::inv_pos). Here it comes from the
    /// rational gaps `CReal.lt` already carries, so both `Exists`es are
    /// eliminated into a `Prop` target — the elimination that *is* permitted.
    pub mul_pos: NameId,

    // --- the multiplicative inverse (ADR-0510 phase F3) ----------------------
    /// `CReal.invShift : Nat → Nat` — `(4k+4)·(k+1) + (4k+3)`, the `C` of the
    /// sampling index `(C+1)·n + C`.
    ///
    /// Written as `(A+1)·b + A` so that `C + 1` **is** `(4k+4)·(k+2)`
    /// definitionally and
    /// [`Rat.nat_index_compose`](crate::RatPrelude::nat_index_compose) applies
    /// to it verbatim, with no ℕ-subtraction anywhere.
    pub inv_shift: NameId,
    /// `CReal.inv : (x : CReal) → (k : Nat) → PosBound x k → CReal` —
    /// `(x⁻¹)_n := (x_{j(n)})⁻¹` at `j(n) = (invShift k + 1)·n + invShift k`.
    ///
    /// **The modulus is data; the proof is only a proof.** A function may take
    /// a `Prop` argument and return a `Type`, and this one does: `k` fixes the
    /// representative outright, and `h` is consumed only inside `CReal.mk`'s
    /// `Prop`-valued regularity field. An `Apart`-indexed inverse would have to
    /// *branch* on a disjunction to choose which reciprocal to compute, which
    /// is the elimination `Or.rec` does not permit — see
    /// [`Self::no_total_inverse`] for the half of the trade that is a theorem,
    /// and [`Self::pos_bound_of_lt`] for why the `k` cannot be recovered from
    /// `0 < x`.
    pub inv: NameId,
    /// `CReal.mul_inv_cancel : ∀ x k (h : PosBound x k),
    /// Equiv (mul x (inv x k h)) one` — **the field law, on the positive
    /// branch**.
    ///
    /// The two sides sample `x` at indices with no relation to each other —
    /// `CReal.mulShift` is built from opaque `Int.natAbs` projections and
    /// `CReal.invShift` from `k` — so it closes through
    /// [`Self::equiv_of_bounded`], where the constant is free, rather than by
    /// an exact estimate.
    pub mul_inv_cancel: NameId,
    /// `CReal.inv_congr : ∀ x y k₁ k₂ h₁ h₂, Equiv x y →
    /// Equiv (inv x k₁ h₁) (inv y k₂ h₂)` — the **sixth congruence
    /// obligation**, and the one that makes `inv` a function on `ℝ` rather than
    /// on representatives.
    ///
    /// Larger than the usual congruence, because the modulus is data: two
    /// callers with different `k` for the same `x` build different sequences,
    /// and the statement quantifies over both independently. It is nonetheless
    /// not an estimate — an inverse in a commutative monoid is unique, so
    /// `mul_inv_cancel` at both ends closes it.
    pub inv_congr: NameId,
    /// `CReal.inv_index_irrelevant : ∀ x k₁ k₂ h₁ h₂,
    /// Equiv (inv x k₁ h₁) (inv x k₂ h₂)`.
    ///
    /// **`x⁻¹` denotes one element of `ℝ`.** `k = 0` samples at `7n+7` and
    /// `k = 1` at `32n+31`; nothing in [`Self::inv`]'s type says the results
    /// agree, and this does. [`Self::inv_congr`] at `y := x`.
    pub inv_index_irrelevant: NameId,

    // --- the lattice (ADR-0519 phase R5) --------------------------------------
    /// `CReal.max : CReal → CReal → CReal` — **pointwise, at the same index**.
    ///
    /// The first operation since [`Self::neg`] that costs no index shift:
    /// `Rat.max` is one-Lipschitz jointly in both arguments
    /// ([`Rat.sub_max_le`](crate::RatPrelude::sub_max_le)), so it does not
    /// degrade the modulus. The decision that `max` looks like it needs is
    /// taken on the **representation**, inside `Rat.max`, never on `CReal`.
    pub max: NameId,
    /// `CReal.min : CReal → CReal → CReal` — the same, through `Rat.min`.
    pub min: NameId,
    /// `CReal.abs : CReal → CReal` — `max x (neg x)`, so it introduces no new
    /// sequence and no new regularity obligation.
    ///
    /// This is the `|·|` ADR-0512 deliberately did without: the module writes
    /// `|r| ≤ q` as the pair `−q ≤ r ∧ r ≤ q` and needs no operator for it.
    /// `abs` exists for the statements that quantify over the magnitude
    /// itself, and it is one-sided throughout —
    /// `Equiv (abs x) x ∨ Equiv (abs x) (neg x)` is a decision on the sign of a
    /// real and is **not** available.
    pub abs: NameId,
    /// `CReal.le_max_left : ∀ x y, le x (max x y)`.
    pub le_max_left: NameId,
    /// `CReal.le_max_right : ∀ x y, le y (max x y)`.
    pub le_max_right: NameId,
    /// `CReal.max_le : ∀ x y z, le x z → le y z → le (max x y) z` — the
    /// universal property of the join, and the only lattice law that needs a
    /// case split (one `Rat.max_cases` per index).
    pub max_le: NameId,
    /// `CReal.min_le_left : ∀ x y, le (min x y) x`.
    pub min_le_left: NameId,
    /// `CReal.min_le_right : ∀ x y, le (min x y) y`.
    pub min_le_right: NameId,
    /// `CReal.le_min : ∀ x y z, le z x → le z y → le z (min x y)`.
    pub le_min: NameId,
    /// `CReal.max_congr : ∀ x x' y y', Equiv x x' → Equiv y y' →
    /// Equiv (max x y) (max x' y')`.
    pub max_congr: NameId,
    /// `CReal.min_congr` — the same for the meet.
    pub min_congr: NameId,
    /// `CReal.abs_congr : ∀ x y, Equiv x y → Equiv (abs x) (abs y)` —
    /// [`Self::max_congr`] with [`Self::neg_congr`] in its second slot.
    pub abs_congr: NameId,
    /// `CReal.le_abs_self : ∀ x, le x (abs x)`.
    pub le_abs_self: NameId,
    /// `CReal.neg_le_abs : ∀ x, le (neg x) (abs x)`.
    pub neg_le_abs: NameId,
    /// `CReal.abs_le : ∀ x z, le x z → le (neg x) z → le (abs x) z` —
    /// [`Self::max_le`] verbatim, and the form every estimate consumes.
    pub abs_le: NameId,
    /// `CReal.abs_nonneg : ∀ x, le zero (abs x)` — the one lattice fact that is
    /// not a rearrangement of the others; it rests on
    /// [`Rat.zero_le_max_neg`](crate::RatPrelude::zero_le_max_neg), the only
    /// consumer of `Rat.le_total` in the development.
    pub abs_nonneg: NameId,
    /// `CReal.not_le_zero_neg_one : Not (le zero (neg one))`.
    ///
    /// A **discrimination**, not a lattice law: it mentions no lattice
    /// operation and exists so [`Self::not_equiv_abs_neg_one`] has something to
    /// contradict. From `add_le_add`, `add_comm`, `add_zero`, `add_neg`,
    /// `le_congr` and `not_le_one_zero` alone.
    pub not_le_zero_neg_one: NameId,
    /// `CReal.not_equiv_abs_neg_one : Not (Equiv (abs (neg one)) (neg one))` —
    /// **`abs` is not the identity function.**
    ///
    /// Every other theorem about `abs` here holds, footprint-free and with its
    /// statement verbatim, of `abs x := x`. This one does not, and it is
    /// derived from [`Self::abs_nonneg`] and the theorem above rather than by
    /// computing on a representative.
    pub not_equiv_abs_neg_one: NameId,

    // --- the Archimedean property (ADR-0512 phase R5) ------------------------
    /// `CReal.ofNat : Nat → CReal := fun n => CReal.ofRat (Rat.natDivSucc n 0)`
    /// — the embedding `ℕ ↪ ℝ`, reusing [`RatPrelude::nat_div_succ`] at
    /// denominator index `0` (`k/(0+1) = k/1`) rather than adding a second
    /// numeral development.
    pub of_nat: NameId,
    /// `CReal.archimedean : ∀ x, ∃ n, CReal.le x (CReal.ofNat n)`.
    ///
    /// The witness is computed, not searched for: `n := CReal.bound x + 1`, the
    /// same magnitude [`Self::bound_within`] already proves bounds `seq x m`
    /// **for every** `m` — so the single inequality `bound_within` supplies is
    /// already stronger than the one index `CReal.le`'s definition asks for,
    /// and no case split on `x`'s sign, and no search over `n`, is needed.
    pub archimedean: NameId,

    // --- density of ℚ in ℝ (ADR-0512 phase R6) --------------------------------
    /// `CReal.rat_approx_upper : ∀ x n, CReal.le x (CReal.ofRat (Rat.add
    /// (CReal.seq x n) (Rat.natDivSucc 1 n)))`.
    ///
    /// `seq x n` plus one modulus is an upper rational bound on `x`, proved
    /// directly from regularity at `(k, n)` with **no** `CReal.add`,
    /// `CReal.neg` or `CReal.abs` — see [`density`](self::density) for why
    /// that shortcut is available here and not for `CReal.add`'s own laws.
    pub rat_approx_upper: NameId,
    /// `CReal.rat_approx_lower : ∀ x n, CReal.le (CReal.ofRat (Rat.sub
    /// (CReal.seq x n) (Rat.natDivSucc 1 n))) x` — the mirror of
    /// [`Self::rat_approx_upper`], read off regularity at `(n, k)`.
    pub rat_approx_lower: NameId,
    /// `CReal.density : ∀ x n, ∃ q : Rat, CReal.le x (CReal.ofRat (Rat.add q
    /// (Rat.natDivSucc 1 n))) ∧ CReal.le (CReal.ofRat (Rat.sub q
    /// (Rat.natDivSucc 1 n))) x`.
    ///
    /// **Density of ℚ in ℝ**, packaged: [`Self::rat_approx_upper`] and
    /// [`Self::rat_approx_lower`] at the witness `q := seq x n`.
    pub density: NameId,

    // --- cotransitivity (ADR-0512 phase R7) -----------------------------------
    /// `CReal.lt_cotrans : ∀ x y, lt x y → ∀ z, Or (lt x z) (lt z y)`.
    ///
    /// Bishop's cotransitivity: the property that makes the strict order
    /// *usable* constructively, since `lt` is not decidable and no `lt_total`
    /// is assumed or provable over `CReal`. Every real `z` can be compared
    /// against the rational gap a `lt x y` witness already carries, via
    /// [`RatPrelude::le_or_lt`](crate::RatPrelude::le_or_lt) — decidability
    /// lives in `ℚ`, not in `ℝ`.
    pub lt_cotrans: NameId,
    /// `CReal.apart_cotrans : ∀ x y, Apart x y → ∀ z, Or (Apart x z) (Apart z y)`.
    ///
    /// Cotransitivity of [`Self::apart`], read off [`Self::lt_cotrans`] in
    /// both `Apart` disjuncts — no new estimate, since `Apart x y := lt x y ∨
    /// lt y x` already carries the case split.
    pub apart_cotrans: NameId,

    // --- Bishop completeness (ADR-0512 phase R8) ------------------------------
    /// `CReal.RegularSeq : (Nat → CReal) → Prop` —
    /// `RegularSeq X := ∀ m n, Within (seq (X m) m − seq (X n) n) (1/(m+1)+1/(n+1))`.
    ///
    /// **The canonical-sample formulation, not the arbitrary-index one.** The
    /// textbook statement compares `X m` and `X n` as reals at an arbitrary
    /// shared representative index (`CReal.le`/`CReal.add`-shaped, the way
    /// [`Self::le`] itself is stated), which routes every consumer through
    /// `CReal.add`'s index shift before it can be unfolded at all. This
    /// definition instead compares the sample **each real already offers at
    /// its own index** — `seq (X m) m`, exactly the quantity
    /// [`Self::rat_approx_upper`]/[`Self::rat_approx_lower`] already prove is
    /// within `1/(m+1)` of the real `X m` — so it is equivalent up to a
    /// constant factor to the textbook condition, never mentions `CReal.add`,
    /// and is what [`Self::limit`] below is built from directly.
    pub regular_seq: NameId,
    /// `CReal.limitSeq : (Nat → CReal) → Nat → Rat` —
    /// `limitSeq X n := seq (X (2n+1)) (2n+1)`.
    ///
    /// The **diagonal**, sampled at Bishop's shift `2n+1` rather than at `n`
    /// itself: [`Self::limit_seq_regular`]'s estimate needs the two halves of
    /// each pairwise bound to fuse via
    /// [`Rat.natDivSucc_halve`](crate::RatPrelude::nat_div_succ_halve) into
    /// exactly `1/(n+1)`, which only happens at this shift — sampling at `n`
    /// leaves a bound twice the size [`Self::regular_pred`] asks for, with no
    /// rearrangement able to close the gap.
    pub limit_seq: NameId,
    /// `CReal.limitSeq_regular : ∀ X, RegularSeq X → Regular (limitSeq X)`.
    ///
    /// **Obligation 1: the diagonal is a `CReal` at all.** The proof needs no
    /// arbitrary third index and no Archimedean closing step — unlike
    /// `Equiv.trans`/`le_trans` — because [`Self::regular_seq`]'s hypothesis
    /// is already stated at the two *fixed* diagonal indices `shift m` and
    /// `shift n`; from there it is one instantiation of `RegularSeq` plus
    /// [`weaken`] against the rational fact `modulus (shift m) (shift n) ≤
    /// modulus m n`.
    pub limit_seq_regular: NameId,
    /// `CReal.limit : (X : Nat → CReal) → RegularSeq X → CReal := fun X h =>
    /// CReal.mk (limitSeq X) (limitSeq_regular X h)`.
    ///
    /// **Bishop completeness, the construction half.** Every `RegularSeq`
    /// sequence of reals has a limit, produced rather than merely asserted to
    /// exist.
    pub limit: NameId,
    /// `CReal.limit_dist : ∀ X (h : RegularSeq X) n k, Within (seq (X n) k −
    /// seq (limit X h) k) (2/(k+1) + 2/(n+1))`.
    ///
    /// **Bishop completeness, the convergence half**, at the rate `X`'s own
    /// regularity carries (`O(1/n)`, uniformly in the sampling index `k`) —
    /// not merely `∀ n, Equiv (X n) (limit ...)`, which is false in general
    /// (a converging sequence is generally not equal to its limit at any
    /// finite `n`). The estimate chains `X n`'s own regularity between `(k,
    /// n)` with one [`Self::regular_seq`] instance at `(n, shift k)`, folds
    /// the two `seq (X n) n` occurrences via `Rat.sub_add_sub`, and widens
    /// `1/(shift k + 1)` up to `1/(k+1)` — no arbitrary third index or
    /// Archimedean lemma needed, for the same reason as
    /// [`Self::limit_seq_regular`].
    pub limit_dist: NameId,

    // --- convergence of sequences of `CReal` (ADR-0512 phase R9) -------------
    /// `CReal.Converges (f : Nat → CReal) (L : CReal) : Prop :=
    /// ∃ (K : Nat), ∀ n, Within (seq (f n) n − seq L n) (Rat.natDivSucc K n)`.
    ///
    /// The canonical-sample, free-constant formulation — see
    /// [`convergence`](self::convergence)'s module documentation for why this
    /// was chosen over the textbook `∀ k, ∃ N, ∀ n ≥ N, …` (that form needs an
    /// antitonicity-in-the-index lemma for `Rat.natDivSucc` this development
    /// deliberately never proves).
    pub converges: NameId,
    /// `CReal.converges_unique : ∀ f L M, Converges f L → Converges f M →
    /// Equiv L M`.
    ///
    /// **The first theorem of analysis over `CReal`**: a limit, when one
    /// exists, is unique up to `Equiv`. One instance of
    /// [`Self::equiv_of_bounded`], no arbitrary third index.
    pub converges_unique: NameId,
    /// `CReal.converges_of_const : ∀ c, Converges (fun _ => c) c`.
    pub converges_of_const: NameId,
    /// `CReal.Cauchy (f : Nat → CReal) : Prop :=
    /// ∃ (K : Nat), ∀ m n, Within (seq (f m) m − seq (f n) n)
    /// (Rat.natDivSucc K m + Rat.natDivSucc K n)`.
    pub cauchy: NameId,
    /// `CReal.converges_cauchy : ∀ f L, Converges f L → Cauchy f`.
    pub converges_cauchy: NameId,

    // --- algebra of limits (ADR-0512 phase R9, continued) --------------------
    /// `CReal.converges_add : ∀ f g L M, Converges f L → Converges g M →
    /// Converges (fun n => add (f n) (g n)) (add L M)`.
    ///
    /// The first algebra-of-limits theorem, and the one the previous slice's
    /// blocker was about: `add`'s Bishop shift means `seq (add (f n) (g n)) n`
    /// samples `f n` and `g n` at `shift n`, not at `n`, so each summand needs
    /// bridging through its own regularity before `Converges`'s hypotheses
    /// apply. See [`convergence`](self::convergence)'s module documentation
    /// for the bridge and the rate constant it costs.
    pub converges_add: NameId,
    /// `CReal.converges_neg : ∀ f L, Converges f L → Converges (fun n => neg
    /// (f n)) (neg L)`.
    ///
    /// Cheap: `neg` is pointwise (no index shift), so this is one
    /// `Rat.bounds_neg` plus the same rewrite [`Self::neg_congr`] already
    /// uses, wrapped in `Converges`'s existential.
    pub converges_neg: NameId,
    /// `CReal.converges_sub : ∀ f g L M, Converges f L → Converges g M →
    /// Converges (fun n => add (f n) (neg (g n))) (add L (neg M))`.
    ///
    /// Immediate from [`Self::converges_add`] and [`Self::converges_neg`].
    /// There is no `CReal.sub` operation in this development, so the
    /// difference is spelled `add _ (neg _)` throughout, honestly.
    pub converges_sub: NameId,

    // --- boundedness of sequences, and sequential continuity (phase R10) ----
    /// `CReal.Bounded (g : Nat → CReal) : Prop :=
    /// ∃ (B : Nat), ∀ (n : Nat), Within (seq (g n) n) (Rat.natDivSucc B 0)`.
    ///
    /// The canonical-sample boundedness a product's variable shift needs
    /// (`CReal.mulShift` scales by a bound on each multiplicand — see
    /// [`convergence`](self::convergence)'s module documentation on
    /// `converges_mul`), stated the same way [`Self::converges`] states its
    /// own modulus: a free `Nat` constant, at the sample's own index.
    pub bounded: NameId,
    /// `CReal.converges_bounded : ∀ f L, Converges f L → Bounded f`.
    ///
    /// A linear-rate convergent sequence is automatically bounded, with no
    /// choice: `Converges f L`'s own witness `K`, widened from `K/(n+1)` to
    /// the constant `K/1`, combines with
    /// [`Self::bound_within`]'s already-constant bound on `L`'s sample.
    pub converges_bounded: NameId,
    /// `CReal.converges_mul : ∀ f g L M, Converges f L → Converges g M →
    /// Converges (fun n => mul (f n) (g n)) (mul L M)`.
    ///
    /// The obstruction was sharper than a missing boundedness hypothesis:
    /// `mul (f n) (g n)` and `mul L M` sample their two factors at
    /// *different* deep indices, so closing this needed the same
    /// arbitrary-third-index estimate [`Self::mul_congr`]/
    /// [`Self::left_distrib`]/[`Self::mul_assoc`] needed —
    /// [`Self::equiv_of_bounded`]'s machinery, reused rather than
    /// re-derived. See [`convergence`](self::convergence)'s module
    /// documentation for the two reusable pieces (`bounded_at_index`,
    /// `converges_gap_at`) this took.
    pub converges_mul: NameId,
    /// `CReal.ContinuousAt (F : CReal → CReal) (x : CReal) : Prop :=
    /// ∀ (g : Nat → CReal), Converges g x → Converges (fun n => F (g n)) (F x)`.
    ///
    /// Sequential continuity, phrased entirely through [`Self::converges`]
    /// rather than a new modulus — mirroring that predicate's own convention
    /// instead of inventing a second one.
    pub continuous_at: NameId,
    /// `CReal.continuous_id : ∀ x, ContinuousAt (fun r => r) x`.
    pub continuous_id: NameId,
    /// `CReal.continuous_const : ∀ c x, ContinuousAt (fun _ => c) x`.
    pub continuous_const: NameId,
    /// `CReal.continuous_add : ∀ F G x, ContinuousAt F x → ContinuousAt G x →
    /// ContinuousAt (fun r => add (F r) (G r)) x`.
    pub continuous_add: NameId,
}

impl CRealPrelude {
    /// The 22 ordered-commutative-ring laws over `CReal`, in the **declaration
    /// order of the `AxReal` package** — the same order
    /// [`RatPrelude::ring_laws`](crate::RatPrelude::ring_laws) uses, so the two
    /// lists line up entry by entry.
    ///
    /// **Thirteen are the `AxReal` package's statements verbatim.** The other
    /// nine — `add_comm`, `add_assoc`, `add_zero`, `add_neg`, `mul_comm`,
    /// `mul_assoc`, `mul_one`, `mul_zero`, `left_distrib` — mention `Eq` in
    /// the axiomatized package and are stated here over
    /// [`CReal.Equiv`](Self::equiv) instead, because `Eq CReal` is **not** the
    /// equality of real numbers. That is ADR-0512's Measurement 2, and it is
    /// the whole reason a setoid was the reachable construction: the laws that
    /// do not mention `Eq` need no restatement at all.
    ///
    /// This list exists so that "22 of 22" is read out of the kernel by a test
    /// rather than asserted in prose.
    #[must_use]
    pub fn ordered_ring_laws(&self) -> [NameId; 22] {
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

fn intern_names(kernel: &mut Kernel, rat: RatPrelude) -> CRealPrelude {
    let anon = kernel.anon();
    let creal = kernel.name_str(anon, "CReal");
    let equiv = kernel.name_str(creal, "Equiv");
    CRealPrelude {
        rat,
        within: kernel.name_str(creal, "Within"),
        regular_pred: kernel.name_str(creal, "Regular"),
        creal,
        mk: kernel.name_str(creal, "mk"),
        rec: kernel.name_str(creal, "rec"),
        seq: kernel.name_str(creal, "seq"),
        regular: kernel.name_str(creal, "regular"),
        equiv,
        equiv_refl: kernel.name_str(equiv, "refl"),
        equiv_symm: kernel.name_str(equiv, "symm"),
        equiv_trans: kernel.name_str(equiv, "trans"),
        of_rat: kernel.name_str(creal, "ofRat"),
        not_zero_one: kernel.name_str(equiv, "not_zero_one"),
        zero: kernel.name_str(creal, "zero"),
        one: kernel.name_str(creal, "one"),
        equiv_of_pointwise: kernel.name_str(equiv, "of_pointwise"),
        neg: kernel.name_str(creal, "neg"),
        neg_congr: kernel.name_str(creal, "neg_congr"),
        neg_le_neg: kernel.name_str(creal, "neg_le_neg"),
        add: kernel.name_str(creal, "add"),
        add_congr: kernel.name_str(creal, "add_congr"),
        add_comm: kernel.name_str(creal, "add_comm"),
        add_neg: kernel.name_str(creal, "add_neg"),
        add_zero: kernel.name_str(creal, "add_zero"),
        add_assoc: kernel.name_str(creal, "add_assoc"),
        of_rat_add: kernel.name_str(creal, "ofRat_add"),
        of_rat_neg: kernel.name_str(creal, "ofRat_neg"),
        of_rat_sub: kernel.name_str(creal, "ofRat_sub"),
        le: kernel.name_str(creal, "le"),
        le_refl: kernel.name_str(creal, "le_refl"),
        le_trans: kernel.name_str(creal, "le_trans"),
        add_le_add: kernel.name_str(creal, "add_le_add"),
        le_of_equiv: kernel.name_str(creal, "le_of_equiv"),
        equiv_of_le_le: kernel.name_str(creal, "equiv_of_le_le"),
        not_le_one_zero: kernel.name_str(creal, "not_le_one_zero"),
        le_add_of_nonneg: kernel.name_str(creal, "le_add_of_nonneg"),
        lt: kernel.name_str(creal, "lt"),
        lt_irrefl: kernel.name_str(creal, "lt_irrefl"),
        lt_trans: kernel.name_str(creal, "lt_trans"),
        lt_of_lt_of_le: kernel.name_str(creal, "lt_of_lt_of_le"),
        lt_of_le_of_lt: kernel.name_str(creal, "lt_of_le_of_lt"),
        le_of_lt: kernel.name_str(creal, "le_of_lt"),
        zero_lt_one: kernel.name_str(creal, "zero_lt_one"),
        add_lt_add_of_le_of_lt: kernel.name_str(creal, "add_lt_add_of_le_of_lt"),
        le_congr: kernel.name_str(creal, "le_congr"),
        lt_congr: kernel.name_str(creal, "lt_congr"),
        bound: kernel.name_str(creal, "bound"),
        bound_within: kernel.name_str(creal, "bound_within"),
        mul_shift: kernel.name_str(creal, "mulShift"),
        mul: kernel.name_str(creal, "mul"),
        equiv_of_bounded: kernel.name_str(equiv, "of_bounded"),
        mul_congr: kernel.name_str(creal, "mul_congr"),
        of_rat_mul: kernel.name_str(creal, "ofRat_mul"),
        mul_comm: kernel.name_str(creal, "mul_comm"),
        mul_one: kernel.name_str(creal, "mul_one"),
        mul_zero: kernel.name_str(creal, "mul_zero"),
        mul_assoc: kernel.name_str(creal, "mul_assoc"),
        mul_le_mul_of_nonneg_left: kernel.name_str(creal, "mul_le_mul_of_nonneg_left"),
        left_distrib: kernel.name_str(creal, "left_distrib"),
        mul_nonneg: kernel.name_str(creal, "mul_nonneg"),
        sq_nonneg: kernel.name_str(creal, "sq_nonneg"),
        neg_mul_neg: kernel.name_str(creal, "neg_mul_neg"),
        not_equiv_mul_one_one_zero: kernel.name_str(creal, "not_equiv_mul_one_one_zero"),
        apart: kernel.name_str(creal, "Apart"),
        apart_symm: kernel.name_str(creal, "apart_symm"),
        apart_irrefl: kernel.name_str(creal, "apart_irrefl"),
        apart_congr: kernel.name_str(creal, "apart_congr"),
        not_equiv_of_apart: kernel.name_str(creal, "not_equiv_of_apart"),
        apart_zero_one: kernel.name_str(creal, "apart_zero_one"),
        no_total_inverse: kernel.name_str(creal, "no_total_inverse"),
        of_rat_le: kernel.name_str(creal, "ofRat_le"),
        pos_bound: kernel.name_str(creal, "PosBound"),
        pos_of_pos_bound: kernel.name_str(creal, "pos_of_pos_bound"),
        pos_bound_of_lt: kernel.name_str(creal, "pos_bound_of_lt"),
        of_rat_pos: kernel.name_str(creal, "ofRat_pos"),
        mul_pos: kernel.name_str(creal, "mul_pos"),
        inv_shift: kernel.name_str(creal, "invShift"),
        inv: kernel.name_str(creal, "inv"),
        mul_inv_cancel: kernel.name_str(creal, "mul_inv_cancel"),
        inv_congr: kernel.name_str(creal, "inv_congr"),
        inv_index_irrelevant: kernel.name_str(creal, "inv_index_irrelevant"),
        max: kernel.name_str(creal, "max"),
        min: kernel.name_str(creal, "min"),
        abs: kernel.name_str(creal, "abs"),
        le_max_left: kernel.name_str(creal, "le_max_left"),
        le_max_right: kernel.name_str(creal, "le_max_right"),
        max_le: kernel.name_str(creal, "max_le"),
        min_le_left: kernel.name_str(creal, "min_le_left"),
        min_le_right: kernel.name_str(creal, "min_le_right"),
        le_min: kernel.name_str(creal, "le_min"),
        max_congr: kernel.name_str(creal, "max_congr"),
        min_congr: kernel.name_str(creal, "min_congr"),
        abs_congr: kernel.name_str(creal, "abs_congr"),
        le_abs_self: kernel.name_str(creal, "le_abs_self"),
        neg_le_abs: kernel.name_str(creal, "neg_le_abs"),
        abs_le: kernel.name_str(creal, "abs_le"),
        abs_nonneg: kernel.name_str(creal, "abs_nonneg"),
        not_le_zero_neg_one: kernel.name_str(creal, "not_le_zero_neg_one"),
        not_equiv_abs_neg_one: kernel.name_str(creal, "not_equiv_abs_neg_one"),
        of_nat: kernel.name_str(creal, "ofNat"),
        archimedean: kernel.name_str(creal, "archimedean"),
        rat_approx_upper: kernel.name_str(creal, "rat_approx_upper"),
        rat_approx_lower: kernel.name_str(creal, "rat_approx_lower"),
        density: kernel.name_str(creal, "density"),
        lt_cotrans: kernel.name_str(creal, "lt_cotrans"),
        apart_cotrans: kernel.name_str(creal, "apart_cotrans"),
        regular_seq: kernel.name_str(creal, "RegularSeq"),
        limit_seq: kernel.name_str(creal, "limitSeq"),
        limit_seq_regular: kernel.name_str(creal, "limitSeq_regular"),
        limit: kernel.name_str(creal, "limit"),
        limit_dist: kernel.name_str(creal, "limit_dist"),
        converges: kernel.name_str(creal, "Converges"),
        converges_unique: kernel.name_str(creal, "converges_unique"),
        converges_of_const: kernel.name_str(creal, "converges_of_const"),
        cauchy: kernel.name_str(creal, "Cauchy"),
        converges_cauchy: kernel.name_str(creal, "converges_cauchy"),
        converges_add: kernel.name_str(creal, "converges_add"),
        converges_neg: kernel.name_str(creal, "converges_neg"),
        converges_sub: kernel.name_str(creal, "converges_sub"),
        bounded: kernel.name_str(creal, "Bounded"),
        converges_bounded: kernel.name_str(creal, "converges_bounded"),
        converges_mul: kernel.name_str(creal, "converges_mul"),
        continuous_at: kernel.name_str(creal, "ContinuousAt"),
        continuous_id: kernel.name_str(creal, "continuous_id"),
        continuous_const: kernel.name_str(creal, "continuous_const"),
        continuous_add: kernel.name_str(creal, "continuous_add"),
    }
}

/// Build the real prelude: `ℝ` as a Bishop setoid over the constructed `ℚ`,
/// **asserting nothing**.
///
/// Idempotent on a kernel that already carries it. A failure rolls the
/// environment back to the pre-call state.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub fn build_creal_prelude(kernel: &mut Kernel) -> Result<CRealPrelude, KernelError> {
    if let Some(PreludeValue::CReal(prelude)) =
        crate::prelude_cache::try_restore(kernel, PreludeKey::CReal)
    {
        return Ok(*prelude);
    }
    build_creal_prelude_uncached(kernel)
}

/// [`build_creal_prelude`] without the process-wide template fast path.
///
/// This is the route that actually runs the trusted gate, and the one the
/// template itself is built through (ADR-0464). The construction is the most
/// expensive in this kernel by four orders of magnitude — measured 2026-08-18 at
/// **44 s** in a debug build against 3.0 ms for `AxReal` — which is exactly why it
/// has a template.
///
/// # Errors
///
/// As [`build_creal_prelude`].
pub(crate) fn build_creal_prelude_uncached(
    kernel: &mut Kernel,
) -> Result<CRealPrelude, KernelError> {
    let rat = build_rat_prelude(kernel)?;
    if let Some(PreludeValue::CReal(prelude)) = kernel.cached_prelude(PreludeKey::CReal)? {
        return Ok(*prelude);
    }
    let prelude = intern_names(kernel, rat);
    if kernel.environment().get(prelude.creal).is_some() {
        return Ok(prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<(), KernelError> {
        let mut d = IntDev::new(kernel, rat.int);
        declare_predicates(&mut d, prelude)?;
        declare_carrier(&mut d, prelude)?;
        declare_projections(&mut d, prelude)?;
        declare_equiv(&mut d, prelude)?;
        declare_reflexivity(&mut d, prelude)?;
        declare_symmetry(&mut d, prelude)?;
        declare_transitivity(&mut d, prelude)?;
        declare_of_rat(&mut d, prelude)?;
        declare_discrimination(&mut d, prelude)?;
        declare_constants(&mut d, prelude)?;
        declare_pointwise(&mut d, prelude)?;
        declare_negation(&mut d, prelude)?;
        declare_addition(&mut d, prelude)?;
        declare_additive_laws(&mut d, prelude)?;
        declare_of_rat_add(&mut d, prelude)?;
        declare_of_rat_neg(&mut d, prelude)?;
        declare_of_rat_sub(&mut d, prelude)?;
        declare_order(&mut d, prelude)?;
        declare_neg_le_neg(&mut d, prelude)?;
        declare_strict_order(&mut d, prelude)?;
        product::declare_product(&mut d, prelude)?;
        field::declare_field(&mut d, prelude)?;
        inverse::declare_inverse(&mut d, prelude)?;
        lattice::declare_lattice(&mut d, prelude)?;
        archimedean::declare_archimedean(&mut d, prelude)?;
        density::declare_density(&mut d, prelude)?;
        cotransitivity::declare_cotransitivity(&mut d, prelude)?;
        completeness::declare_completeness(&mut d, prelude)?;
        convergence::declare_convergence(&mut d, prelude)
    })();
    match built {
        Ok(()) => {
            kernel.register_prelude(
                PreludeKey::CReal,
                PreludeValue::CReal(Box::new(prelude)),
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

// --- term builders ----------------------------------------------------------

/// `Nat → Rat`, the representative type. Its own sort is `Type 0`, so a field of
/// this type does not push the carrier up a universe.
fn seq_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    d.arrow(nat, carrier)
}

/// `CReal`.
fn creal_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.creal, vec![])
}

/// `CReal.Within r q`.
fn within(d: &mut IntDev<'_>, p: CRealPrelude, r: ExprId, q: ExprId) -> ExprId {
    d.const_app(p.within, &[r, q])
}

/// `CReal.seq x n`.
fn sample(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.seq, &[x, n])
}

/// `Rat.natDivSucc k j`, with `k` a literal.
fn div_succ(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, j: ExprId) -> ExprId {
    let numerator = d.num(k);
    d.const_app(p.rat.nat_div_succ, &[numerator, j])
}

/// `Rat.add (natDivSucc 1 m) (natDivSucc 1 n)` — the regularity modulus,
/// written inline rather than behind a constant so the rearrangement in
/// [`declare_transitivity`] sees the two summands.
fn modulus(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId, n: ExprId) -> ExprId {
    let left = div_succ(d, p, 1, m);
    let right = div_succ(d, p, 1, n);
    radd(d, left, right)
}

/// `CReal.Equiv x y`.
fn equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.equiv, &[x, y])
}

/// `And.intro`, at two `Prop`s.
fn and_intro(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    left: ExprId,
    right: ExprId,
    lp: ExprId,
    rp: ExprId,
) -> ExprId {
    let intro = p.rat.int.logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

/// The lower and upper halves of a `Within r q` proof.
fn halves(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    r: ExprId,
    q: ExprId,
    proof: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let negated = rneg(d, q);
    let lower = crate::rat_prelude::ops::rle(d, rat, negated, r);
    let upper = crate::rat_prelude::ops::rle(d, rat, r, q);
    let left = d.and_left(lower, upper, proof);
    let right = d.and_right(lower, upper, proof);
    (left, right)
}

/// Widen a two-sided bound: from `Within r q` and `q ≤ q'`, `Within r q'`.
///
/// The one thing the `−b ≤ a ∧ a ≤ b` encoding needs that an `abs` operator
/// would give for free, and it is four lines: the upper half is `le_trans`
/// outright, the lower half is `le_trans` after `neg_le_neg` turns `q ≤ q'`
/// into `−q' ≤ −q`.
fn weaken(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    r: ExprId,
    bound: ExprId,
    wider: ExprId,
    proof: ExprId,
    order: ExprId,
) -> ExprId {
    let rat = p.rat;
    let rle = crate::rat_prelude::ops::rle;
    let (lower, upper) = halves(d, p, r, bound, proof);
    let widened = d.lemma(rat.le_trans, &[r, bound, wider, upper, order]);
    let negated_wide = rneg(d, wider);
    let negated_bound = rneg(d, bound);
    let flipped = d.lemma(rat.neg_le_neg, &[bound, wider, order]);
    let deepened = d.lemma(
        rat.le_trans,
        &[negated_wide, negated_bound, r, flipped, lower],
    );
    let lower_ty = rle(d, rat, negated_wide, r);
    let upper_ty = rle(d, rat, r, wider);
    and_intro(d, p, lower_ty, upper_ty, deepened, widened)
}

/// `1/(2n+2) + 1/(n+1) ≤ 2/(n+1)` — the single inequality that both `add_zero`
/// and `add_assoc` reduce to.
///
/// Both laws compare a sample at Bishop's shifted index `2n+1` with one at `n`,
/// and regularity bounds that difference by `1/(2n+2) + 1/(n+1)` where the
/// setoid asks for `2/(n+1)`. Read at the common denominator `2n+2` — which is
/// what [`Rat.natDivSucc_halve`](crate::RatPrelude::nat_div_succ_halve)
/// supplies, `1/(n+1) = 2/(2n+2)` — the two sides are `3/(2n+2)` and `4/(2n+2)`,
/// so the gap is one `1/(2n+2)` and closing it needs only nonnegativity. **No
/// monotonicity of `natDivSucc` in its index is required**, which is what makes
/// these two laws cost a helper rather than a new rational development.
///
/// Returns a proof of `Rat.le (modulus (2n+1) n) (natDivSucc 2 n)`.
fn shifted_bound_le(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let rat = p.rat;
    let rle = crate::rat_prelude::ops::rle;
    let s = shift(d, n);
    let one_s = div_succ(d, p, 1, s);
    let two_s = div_succ(d, p, 2, s);
    let three_s = div_succ(d, p, 3, s);
    let four_s = div_succ(d, p, 4, s);
    let one_n = div_succ(d, p, 1, n);
    let two_n = div_succ(d, p, 2, n);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three_nat = d.num(3);

    // `1/(n+1) = 2/(2n+2)`: the halving identity, read backwards.
    let halve = d.lemma(rat.nat_div_succ_halve, &[n]);
    let deepen = rsymm(d, two_s, one_n, halve);

    // Left: `1/(2n+2) + 1/(n+1) = 1/(2n+2) + 2/(2n+2) = 3/(2n+2)`.
    let start = radd(d, one_s, one_n);
    let staged = radd(d, one_s, two_s);
    let step = rcongr(d, one_n, two_s, deepen, &|d, t| radd(d, one_s, t));
    let fuse_left = d.lemma(rat.nat_div_succ_add, &[one_nat, two_nat, s]);
    let (_, left_chain) = rchain(d, start, &[(staged, step), (three_s, fuse_left)]);

    // Right: `2/(n+1) = 1/(n+1) + 1/(n+1) = 2/(2n+2) + 2/(2n+2) = 4/(2n+2)`.
    let split = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
    let doubled_n = radd(d, one_n, one_n);
    let unsplit = rsymm(d, doubled_n, two_n, split);
    let first = rcongr(d, one_n, two_s, deepen, &|d, t| radd(d, t, one_n));
    let mixed = radd(d, two_s, one_n);
    let second = rcongr(d, one_n, two_s, deepen, &|d, t| radd(d, two_s, t));
    let doubled_s = radd(d, two_s, two_s);
    let fuse_right = d.lemma(rat.nat_div_succ_add, &[two_nat, two_nat, s]);
    let (_, right_chain) = rchain(
        d,
        two_n,
        &[
            (doubled_n, unsplit),
            (mixed, first),
            (doubled_s, second),
            (four_s, fuse_right),
        ],
    );

    // `3/(2n+2) ≤ 3/(2n+2) + 1/(2n+2) = 4/(2n+2)`.
    let zero = rzero(d, rat);
    let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, s]);
    let reflexive = d.lemma(rat.le_refl, &[three_s]);
    let padded = d.lemma(
        rat.add_le_add,
        &[three_s, three_s, zero, one_s, reflexive, nonneg],
    );
    let with_zero = radd(d, three_s, zero);
    let sum = radd(d, three_s, one_s);
    let collapse = d.lemma(rat.add_zero, &[three_s]);
    let trimmed = rat_eq_rewrite(d, with_zero, three_s, collapse, padded, &|d, t| {
        rle(d, rat, t, sum)
    });
    let fuse_gap = d.lemma(rat.nat_div_succ_add, &[three_nat, one_nat, s]);
    let core = rat_eq_rewrite(d, sum, four_s, fuse_gap, trimmed, &|d, t| {
        rle(d, rat, three_s, t)
    });

    // Read both endpoints back at their original denominators.
    let widen_left = rsymm(d, start, three_s, left_chain);
    let moved = rat_eq_rewrite(d, three_s, start, widen_left, core, &|d, t| {
        rle(d, rat, t, four_s)
    });
    let widen_right = rsymm(d, two_n, four_s, right_chain);
    rat_eq_rewrite(d, four_s, two_n, widen_right, moved, &|d, t| {
        rle(d, rat, start, t)
    })
}

/// The **quantity** half of Bishop's four-term estimate:
/// `(a − p) + ((p − q) + ((q − r) + (r − b))) = a − b`, three applications of
/// the telescoping identity from the inside out.
///
/// Returns `(start, target, proof)` with `proof : Eq Rat start target`. Nothing
/// here is a rearrangement — the four differences are combined right-nested
/// precisely so that they chain — and nothing here depends on *which* bound
/// each difference carries, which is why the two-sided `Equiv.trans` and the
/// one-sided [`CReal.le_trans`](CRealPrelude::le_trans) share it verbatim.
fn telescope_four(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    head: ExprId,
    first_mid: ExprId,
    second_mid: ExprId,
    third_mid: ExprId,
    tail: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let u1 = rsub(d, rat, head, first_mid);
    let u2 = rsub(d, rat, first_mid, second_mid);
    let u3 = rsub(d, rat, second_mid, third_mid);
    let u4 = rsub(d, rat, third_mid, tail);
    let q34 = radd(d, u3, u4);
    let q234 = radd(d, u2, q34);
    let q1234 = radd(d, u1, q234);
    let target = rsub(d, rat, head, tail);

    let mid_second = rsub(d, rat, second_mid, tail);
    let mid_first = rsub(d, rat, first_mid, tail);
    let step34 = d.lemma(rat.sub_add_sub, &[second_mid, third_mid, tail]);
    let step234 = d.lemma(rat.sub_add_sub, &[first_mid, second_mid, tail]);
    let step1234 = d.lemma(rat.sub_add_sub, &[head, first_mid, tail]);
    let q234_reduced = radd(d, u2, mid_second);
    let staged = radd(d, u1, q234_reduced);
    let first = rcongr(d, q34, mid_second, step34, &|d, t| {
        let inner = radd(d, u2, t);
        radd(d, u1, inner)
    });
    let second = rcongr(d, q234_reduced, mid_first, step234, &|d, t| radd(d, u1, t));
    let q1234_reduced = radd(d, u1, mid_first);
    let (_, quantity) = rchain(
        d,
        q1234,
        &[(staged, first), (q1234_reduced, second), (target, step1234)],
    );
    (q1234, target, quantity)
}

/// The **bound** half of Bishop's four-term estimate:
/// `(1/(n+1) + 1/(j+1)) + (2/(j+1) + (2/(j+1) + (1/(j+1) + 1/(n+1))))` fused
/// into `2/(n+1) + 6/(j+1)`, which is the form the Archimedean lemma consumes.
///
/// Returns `(start, target, proof)` with `proof : Eq Rat start target`. Six
/// summands over two denominators; `rsum_perm` sorts them and
/// `Rat.natDivSucc_add` fuses each group, and the sort is done by the shared
/// helper rather than inline because that is where a proof of this size goes
/// wrong silently.
fn six_term_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    n: ExprId,
    j: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let b1 = modulus(d, p, n, j);
    let b2 = div_succ(d, p, 2, j);
    let b3 = div_succ(d, p, 2, j);
    let b4 = modulus(d, p, j, n);
    let c34 = radd(d, b3, b4);
    let c234 = radd(d, b2, c34);
    let c1234 = radd(d, b1, c234);
    // The bound rearranges: (A+Bj) + (Cj + (Cj + (Bj+A))) = 2/(n+1) + 6/(j+1).
    let a_atom = div_succ(d, p, 1, n);
    let b_atom = div_succ(d, p, 1, j);
    let c_atom = div_succ(d, p, 2, j);
    let flat_atoms = [a_atom, b_atom, c_atom, c_atom, b_atom, a_atom];
    let sorted_atoms = [a_atom, a_atom, b_atom, c_atom, c_atom, b_atom];
    let flatten = rsum_append(d, rat, &flat_atoms[..2], &flat_atoms[2..]);
    let flat = rsum(d, rat, &flat_atoms);
    let permute = rsum_perm(d, rat, &flat_atoms, &sorted_atoms);
    let sorted = rsum(d, rat, &sorted_atoms);

    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three = div_succ(d, p, 3, j);
    let five = div_succ(d, p, 5, j);
    let six = div_succ(d, p, 6, j);
    let fuse_inner = d.lemma(rat.nat_div_succ_add, &[two_nat, one_nat, j]);
    let cb = radd(d, c_atom, b_atom);
    let after_inner = rcongr(d, cb, three, fuse_inner, &|d, t| {
        let level1 = radd(d, c_atom, t);
        let level2 = radd(d, b_atom, level1);
        let level3 = radd(d, a_atom, level2);
        radd(d, a_atom, level3)
    });
    let sorted_1 = {
        let level1 = radd(d, c_atom, three);
        let level2 = radd(d, b_atom, level1);
        let level3 = radd(d, a_atom, level2);
        radd(d, a_atom, level3)
    };
    let three_nat = d.num(3);
    let fuse_mid = d.lemma(rat.nat_div_succ_add, &[two_nat, three_nat, j]);
    let c3 = radd(d, c_atom, three);
    let after_mid = rcongr(d, c3, five, fuse_mid, &|d, t| {
        let level2 = radd(d, b_atom, t);
        let level3 = radd(d, a_atom, level2);
        radd(d, a_atom, level3)
    });
    let sorted_2 = {
        let level2 = radd(d, b_atom, five);
        let level3 = radd(d, a_atom, level2);
        radd(d, a_atom, level3)
    };
    let five_nat = d.num(5);
    let fuse_outer = d.lemma(rat.nat_div_succ_add, &[one_nat, five_nat, j]);
    let b5 = radd(d, b_atom, five);
    let after_outer = rcongr(d, b5, six, fuse_outer, &|d, t| {
        let level3 = radd(d, a_atom, t);
        radd(d, a_atom, level3)
    });
    let sorted_3 = {
        let level3 = radd(d, a_atom, six);
        radd(d, a_atom, level3)
    };
    let regroup = {
        let forward = d.lemma(rat.add_assoc, &[a_atom, a_atom, six]);
        let flat_pair = {
            let aa = radd(d, a_atom, a_atom);
            radd(d, aa, six)
        };
        rsymm(d, flat_pair, sorted_3, forward)
    };
    let aa = radd(d, a_atom, a_atom);
    let flat_pair = radd(d, aa, six);
    let fuse_head = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
    let head_bound = div_succ(d, p, 2, n);
    let after_head = rcongr(d, aa, head_bound, fuse_head, &|d, t| radd(d, t, six));
    let final_bound = radd(d, head_bound, six);
    let (_, bound_chain) = rchain(
        d,
        c1234,
        &[
            (flat, flatten),
            (sorted, permute),
            (sorted_1, after_inner),
            (sorted_2, after_mid),
            (sorted_3, after_outer),
            (flat_pair, regroup),
            (final_bound, after_head),
        ],
    );
    (c1234, final_bound, bound_chain)
}

// --- the definitions --------------------------------------------------------

/// `CReal.Within` and `CReal.Regular`.
fn declare_predicates(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = rat_ty(d);
    let prop = d.kernel().sort_zero();

    // Within r q := And (Rat.le (Rat.neg q) r) (Rat.le r q)
    {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let negated = rneg(d, q);
        let lower = crate::rat_prelude::ops::rle(d, rat, negated, r);
        let upper = crate::rat_prelude::ops::rle(d, rat, r, q);
        let body = d.and(lower, upper);
        let value = {
            let with_q = d.lam_fv(q_fv, carrier, body);
            d.lam_fv(r_fv, carrier, with_q)
        };
        let ty = {
            let inner = d.arrow(carrier, prop);
            d.arrow(carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.within,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })?;
    }

    // Regular f := ∀ (m n : Nat), Within (Rat.sub (f m) (f n)) (1/(m+1) + 1/(n+1))
    {
        let nat = d.nat_ty();
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let left = d.apply(f, &[m]);
        let right = d.apply(f, &[n]);
        let difference = rsub(d, rat, left, right);
        let bound = modulus(d, p, m, n);
        let claim = within(d, p, difference, bound);
        let body = {
            let over_n = d.pi_fv(n_fv, nat, claim);
            d.pi_fv(m_fv, nat, over_n)
        };
        let sequences = seq_ty(d);
        let value = d.lam_fv(f_fv, sequences, body);
        let ty = d.arrow(sequences, prop);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.regular_pred,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
        })?;
    }
    Ok(())
}

/// The carrier: a one-constructor inductive in `Type 0` with a function field
/// and a dependent `Prop` field over it.
fn declare_carrier(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let sequences = seq_ty(d);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    let mk_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let regular = d.const_app(p.regular_pred, &[f]);
        let result = creal_ty(d, p);
        let body = d.arrow(regular, result);
        d.pi_fv(f_fv, sequences, body)
    };
    d.kernel()
        .add_inductive(p.creal, &[], 0, type0, &[(p.mk, mk_ty)])
}

/// The two projections: the representative (large elimination, into `Type 0`)
/// and its regularity proof (into `Prop`).
fn declare_projections(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let sequences = seq_ty(d);
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let anon = d.anon_name();
    let carrier = creal_ty(d, p);

    // seq x := CReal.rec (fun _ => Nat → Rat) (fun f _ => f) x
    {
        let motive = d
            .kernel()
            .lam(anon, carrier, sequences, BinderInfo::Default);
        let minor = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let regular = d.const_app(p.regular_pred, &[f]);
            let inner = d.kernel().lam(anon, regular, f, BinderInfo::Default);
            d.lam_fv(f_fv, sequences, inner)
        };
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, x]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = d.arrow(carrier, sequences);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.seq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 1),
        })?;
    }

    // regular x : Regular (seq x) := CReal.rec (fun y => Regular (seq y)) (fun f h => h) x
    {
        let claim = |d: &mut IntDev<'_>, y: ExprId| {
            let representative = d.const_app(p.seq, &[y]);
            d.const_app(p.regular_pred, &[representative])
        };
        let motive = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = claim(d, y);
            d.lam_fv(y_fv, carrier, body)
        };
        let minor = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let regular = d.const_app(p.regular_pred, &[f]);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let inner = d.lam_fv(h_fv, regular, h);
            d.lam_fv(f_fv, sequences, inner)
        };
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let rec = d.kernel().const_(p.rec, vec![zero_level]);
        let body = d.apply(rec, &[motive, minor, x]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let inner = claim(d, x);
            d.pi_fv(x_fv, carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.regular,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `CReal.Equiv x y := ∀ n, Within (seq x n − seq y n) (2/(n+1))`.
fn declare_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let left = sample(d, p, x, n);
    let right = sample(d, p, y, n);
    let difference = rsub(d, p.rat, left, right);
    let bound = div_succ(d, p, 2, n);
    let claim = within(d, p, difference, bound);
    let body = d.pi_fv(n_fv, nat, claim);
    let value = {
        let with_y = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let inner = d.arrow(carrier, prop);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.equiv,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 2),
    })
}

/// `Equiv.refl`: `seq x n − seq x n = 0`, and `0` is inside every bound.
fn declare_reflexivity(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let point = sample(d, p, x, n);
    let difference = rsub(d, rat, point, point);
    let bound = div_succ(d, p, 2, n);
    let zero = rzero(d, rat);
    let negated = rneg(d, bound);

    let collapse = d.lemma(rat.sub_self, &[point]);
    let back = rsymm(d, difference, zero, collapse);
    let two = d.num(2);
    let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
    let nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, nonneg]);
    let lower = rat_eq_rewrite(d, zero, difference, back, nonpos, &|d, t| {
        crate::rat_prelude::ops::rle(d, rat, negated, t)
    });
    let upper = rat_eq_rewrite(d, zero, difference, back, nonneg, &|d, t| {
        crate::rat_prelude::ops::rle(d, rat, t, bound)
    });
    let lower_ty = crate::rat_prelude::ops::rle(d, rat, negated, difference);
    let upper_ty = crate::rat_prelude::ops::rle(d, rat, difference, bound);
    let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
    let value = {
        let over_n = d.lam_fv(n_fv, nat, pair);
        d.lam_fv(x_fv, carrier, over_n)
    };
    let ty = {
        let inner = equiv(d, p, x, x);
        d.pi_fv(x_fv, carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_refl,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv.symm`: negate the two-sided bound, then `−(a − b) = b − a`.
fn declare_symmetry(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let hypothesis = equiv(d, p, x, y);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let a = sample(d, p, x, n);
    let b = sample(d, p, y, n);
    let forward = rsub(d, rat, a, b);
    let backward = rsub(d, rat, b, a);
    let bound = div_succ(d, p, 2, n);
    let instance = d.apply(h, &[n]);
    let (lower, upper) = halves(d, p, forward, bound, instance);
    let flipped = d.lemma(rat.bounds_neg, &[forward, bound, lower, upper]);
    let negated_forward = rneg(d, forward);
    let rewrite = d.lemma(rat.neg_sub, &[a, b]);
    let body = rat_eq_rewrite(d, negated_forward, backward, rewrite, flipped, &|d, t| {
        within(d, p, t, bound)
    });
    let value = {
        let over_n = d.lam_fv(n_fv, nat, body);
        let with_h = d.lam_fv(h_fv, hypothesis, over_n);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, y, x);
        let inner = d.arrow(hypothesis, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_symm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv.trans`: Bishop's four-term estimate at an arbitrary index `j`,
/// closed by the Archimedean property of `ℚ`.
fn declare_transitivity(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rle = crate::rat_prelude::ops::rle;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let first_ty = equiv(d, p, x, y);
    let second_ty = equiv(d, p, y, z);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);
    let hyz_fv = d.fresh_fvar();
    let hyz = d.kernel().fvar(hyz_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let head = sample(d, p, x, n);
    let tail = sample(d, p, z, n);
    let target = rsub(d, rat, head, tail);
    let goal_bound = div_succ(d, p, 2, n);

    // The estimate at an arbitrary index `j`, as a function of `j`.
    let estimate = |d: &mut IntDev<'_>, j: ExprId| -> (ExprId, ExprId) {
        let xj = sample(d, p, x, j);
        let yj = sample(d, p, y, j);
        let zj = sample(d, p, z, j);
        let u1 = rsub(d, rat, head, xj);
        let u2 = rsub(d, rat, xj, yj);
        let u3 = rsub(d, rat, yj, zj);
        let u4 = rsub(d, rat, zj, tail);
        let b1 = modulus(d, p, n, j);
        let b2 = div_succ(d, p, 2, j);
        let b3 = div_succ(d, p, 2, j);
        let b4 = modulus(d, p, j, n);

        let w1 = d.lemma(p.regular, &[x, n, j]);
        let w2 = d.apply(hxy, &[j]);
        let w3 = d.apply(hyz, &[j]);
        let w4 = d.lemma(p.regular, &[z, j, n]);

        let (l1, r1) = halves(d, p, u1, b1, w1);
        let (l2, r2) = halves(d, p, u2, b2, w2);
        let (l3, r3) = halves(d, p, u3, b3, w3);
        let (l4, r4) = halves(d, p, u4, b4, w4);

        // Combine right-nested, so the quantities telescope in the same order.
        let w34 = d.lemma(rat.bounds_add, &[u3, b3, u4, b4, l3, r3, l4, r4]);
        let q34 = radd(d, u3, u4);
        let c34 = radd(d, b3, b4);
        let (l34, r34) = halves(d, p, q34, c34, w34);
        let w234 = d.lemma(rat.bounds_add, &[u2, b2, q34, c34, l2, r2, l34, r34]);
        let q234 = radd(d, u2, q34);
        let c234 = radd(d, b2, c34);
        let (l234, r234) = halves(d, p, q234, c234, w234);
        let w1234 = d.lemma(rat.bounds_add, &[u1, b1, q234, c234, l1, r1, l234, r234]);
        let q1234 = radd(d, u1, q234);
        let c1234 = radd(d, b1, c234);

        // The quantity telescopes and the bound fuses — both are functions of
        // the five sample points and of `(n, j)` alone, so both are shared with
        // `CReal.le_trans`, which runs the *upper half* of this same estimate.
        let (_, _, quantity) = telescope_four(d, p, head, xj, yj, zj, tail);
        let (_, final_bound, bound_chain) = six_term_bound(d, p, n, j);

        let at_quantity = rat_eq_rewrite(d, q1234, target, quantity, w1234, &|d, t| {
            within(d, p, t, c1234)
        });
        let moved = rat_eq_rewrite(d, c1234, final_bound, bound_chain, at_quantity, &|d, t| {
            within(d, p, target, t)
        });
        (final_bound, moved)
    };

    // Upper half: `∀ j, target ≤ 2/(n+1) + 6/(j+1)`, then the Archimedean lemma.
    let six_nat = d.num(6);
    let upper_hypothesis = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let (bound, proof) = estimate(d, j);
        let (_, upper) = halves(d, p, target, bound, proof);
        d.lam_fv(j_fv, nat, upper)
    };
    let upper = d.lemma(
        rat.le_of_le_add_nat_div_succ,
        &[target, goal_bound, six_nat, upper_hypothesis],
    );

    // Lower half: negate the estimate, run the same lemma, and negate back.
    let negated_target = rneg(d, target);
    let lower_hypothesis = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let (bound, proof) = estimate(d, j);
        let (low, high) = halves(d, p, target, bound, proof);
        let flipped = d.lemma(rat.bounds_neg, &[target, bound, low, high]);
        let negated_bound = rneg(d, bound);
        let inner_lower = rle(d, rat, negated_bound, negated_target);
        let inner_upper = rle(d, rat, negated_target, bound);
        let body = d.and_right(inner_lower, inner_upper, flipped);
        d.lam_fv(j_fv, nat, body)
    };
    let lower_raw = d.lemma(
        rat.le_of_le_add_nat_div_succ,
        &[negated_target, goal_bound, six_nat, lower_hypothesis],
    );
    let lower_negated = d.lemma(rat.neg_le_neg, &[negated_target, goal_bound, lower_raw]);
    let twice = rneg(d, negated_target);
    let cancel = d.lemma(rat.neg_neg, &[target]);
    let negated_goal = rneg(d, goal_bound);
    let lower = rat_eq_rewrite(d, twice, target, cancel, lower_negated, &|d, t| {
        rle(d, rat, negated_goal, t)
    });

    let lower_ty = rle(d, rat, negated_goal, target);
    let upper_ty = rle(d, rat, target, goal_bound);
    let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
    let value = {
        let over_n = d.lam_fv(n_fv, nat, pair);
        let with_second = d.lam_fv(hyz_fv, second_ty, over_n);
        let with_first = d.lam_fv(hxy_fv, first_ty, with_second);
        let with_z = d.lam_fv(z_fv, carrier, with_first);
        let with_y = d.lam_fv(y_fv, carrier, with_z);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, x, z);
        let after_second = d.arrow(second_ty, conclusion);
        let after_first = d.arrow(first_ty, after_second);
        let with_z = d.pi_fv(z_fv, carrier, after_first);
        let with_y = d.pi_fv(y_fv, carrier, with_z);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_trans,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.ofRat q` — the constant sequence, and with it the proof that the
/// carrier is **inhabited**.
///
/// The regularity obligation is `Within (q − q) (1/(m+1) + 1/(n+1))`, and
/// `q − q` is `0` by `Rat.sub_self`, so it reduces to "`0` is inside a
/// nonnegative bound".
fn declare_of_rat(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let rle = crate::rat_prelude::ops::rle;

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sequences = seq_ty(d);
    let constant = {
        let anon = d.anon_name();
        d.kernel().lam(anon, nat, q, BinderInfo::Default)
    };
    let regularity = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let difference = rsub(d, rat, q, q);
        let bound = modulus(d, p, m, n);
        let zero = rzero(d, rat);
        let negated = rneg(d, bound);
        let one_nat = d.num(1);
        let left_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, m]);
        let right_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, n]);
        let left_atom = div_succ(d, p, 1, m);
        let right_atom = div_succ(d, p, 1, n);
        let nonneg = d.lemma(
            rat.add_nonneg,
            &[left_atom, right_atom, left_nonneg, right_nonneg],
        );
        let nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, nonneg]);
        let collapse = d.lemma(rat.sub_self, &[q]);
        let back = rsymm(d, difference, zero, collapse);
        let lower = rat_eq_rewrite(d, zero, difference, back, nonpos, &|d, t| {
            rle(d, rat, negated, t)
        });
        let upper = rat_eq_rewrite(d, zero, difference, back, nonneg, &|d, t| {
            rle(d, rat, t, bound)
        });
        let lower_ty = rle(d, rat, negated, difference);
        let upper_ty = rle(d, rat, difference, bound);
        let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
        let over_n = d.lam_fv(n_fv, nat, pair);
        d.lam_fv(m_fv, nat, over_n)
    };
    let constructor = d.kernel().const_(p.mk, vec![]);
    let body = d.apply(constructor, &[constant, regularity]);
    let value = d.lam_fv(q_fv, carrier, body);
    let result = creal_ty(d, p);
    let ty = d.arrow(carrier, result);
    let _ = sequences;
    d.kernel().add_declaration(Declaration::Definition {
        name: p.of_rat,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 3),
    })
}

/// `Not (CReal.Equiv (ofRat 0) (ofRat 1))` — `Equiv` is not the total relation.
///
/// Read at index `3`, the hypothesis' lower half says `−1/2 ≤ 0 − 1`, i.e.
/// `−1/2 ≤ −1`. Every term in that is closed, so `Rat.le` unfolds through
/// `Int.le` to `Nat.le 1 0` by pure reduction and `Nat.not_succ_le_zero`
/// finishes it. Nothing in the proof is specific to the construction beyond
/// `CReal.seq (ofRat q) n` reducing to `q`, which is the point.
fn declare_discrimination(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = rat.int.nat;

    let zero_rat = rzero(d, rat);
    let one_rat = d.kernel().const_(rat.one, vec![]);
    let left = d.const_app(p.of_rat, &[zero_rat]);
    let right = d.const_app(p.of_rat, &[one_rat]);
    let claim = equiv(d, p, left, right);
    let stmt = d.not(claim);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let index = d.num(3);
    let instance = d.apply(h, &[index]);
    let a = sample(d, p, left, index);
    let b = sample(d, p, right, index);
    let difference = rsub(d, rat, a, b);
    let bound = div_succ(d, p, 2, index);
    let (lower, _upper) = halves(d, p, difference, bound, instance);
    // `lower : Rat.le (-1/2) (-1)`, which reduces to `Nat.le 1 0`.
    let zero_nat = d.zero();
    let absurd = d.lemma(nat.not_succ_le_zero, &[zero_nat, lower]);
    let value = d.lam_fv(h_fv, claim, absurd);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.not_zero_one,
        uparams: vec![],
        ty: stmt,
        value,
    })
}

mod archimedean;
mod completeness;
mod convergence;
mod cotransitivity;
mod density;
mod field;
mod inverse;
mod lattice;
mod product;

#[cfg(test)]
mod creal_tests;

// --- the additive structure -------------------------------------------------

/// `CReal.zero` and `CReal.one`, as constant sequences.
fn declare_constants(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let result = creal_ty(d, p);
    let constant = |d: &mut IntDev<'_>, name: NameId, source: NameId| -> Result<(), KernelError> {
        let value_rat = d.kernel().const_(source, vec![]);
        let value = d.const_app(p.of_rat, &[value_rat]);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty: result,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 4),
        })
    };
    constant(d, p.zero, rat.zero)?;
    constant(d, p.one, rat.one)
}

/// `Equiv.of_pointwise`: two reals whose representatives agree at every index
/// are `Equiv`-equal.
///
/// The converse is **false** — `CReal.Equiv` relates sequences that are merely
/// asymptotically close — which is exactly why the carrier is a setoid and not
/// a quotient. This direction is what makes the pointwise laws free.
fn declare_pointwise(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rle = crate::rat_prelude::ops::rle;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let hypothesis = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let left = sample(d, p, x, n);
        let right = sample(d, p, y, n);
        let claim = crate::rat_prelude::ops::req(d, left, right);
        d.pi_fv(n_fv, nat, claim)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let a = sample(d, p, x, n);
    let b = sample(d, p, y, n);
    let difference = rsub(d, rat, a, b);
    let bound = div_succ(d, p, 2, n);
    let zero = rzero(d, rat);
    let negated = rneg(d, bound);

    let pointwise = d.apply(h, &[n]);
    let degenerate = rsub(d, rat, b, b);
    let step = rcongr(d, a, b, pointwise, &|d, t| rsub(d, rat, t, b));
    let collapse = d.lemma(rat.sub_self, &[b]);
    let (_, to_zero) = rchain(d, difference, &[(degenerate, step), (zero, collapse)]);
    let back = rsymm(d, difference, zero, to_zero);
    let two = d.num(2);
    let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
    let nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, nonneg]);
    let lower = rat_eq_rewrite(d, zero, difference, back, nonpos, &|d, t| {
        rle(d, rat, negated, t)
    });
    let upper = rat_eq_rewrite(d, zero, difference, back, nonneg, &|d, t| {
        rle(d, rat, t, bound)
    });
    let lower_ty = rle(d, rat, negated, difference);
    let upper_ty = rle(d, rat, difference, bound);
    let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
    let value = {
        let over_n = d.lam_fv(n_fv, nat, pair);
        let with_h = d.lam_fv(h_fv, hypothesis, over_n);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, x, y);
        let inner = d.arrow(hypothesis, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_of_pointwise,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.neg`, and its `Equiv`-congruence.
///
/// Negation is the one operation that needs **no index shift**: it does not
/// degrade the modulus, because `(−x_m) − (−x_n)` is `x_n − x_m` and the
/// regularity bound is symmetric in its two indices. `CReal.add` will not be so
/// lucky — Bishop's `(x+y)_n := x_{2n+1} + y_{2n+1}` exists precisely because
/// adding two regular sequences doubles the error.
fn declare_negation(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let sequences = seq_ty(d);
    let rle = crate::rat_prelude::ops::rle;

    // neg x := mk (fun n => Rat.neg (seq x n)) _
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let representative = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let point = sample(d, p, x, n);
            let body = rneg(d, point);
            d.lam_fv(n_fv, nat, body)
        };
        let regularity = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let xm = sample(d, p, x, m);
            let xn = sample(d, p, x, n);
            let negated_m = rneg(d, xm);
            let negated_n = rneg(d, xn);
            let goal_quantity = rsub(d, rat, negated_m, negated_n);
            let goal_bound = modulus(d, p, m, n);

            // `regular x n m` bounds `x_n − x_m` by `1/(n+1) + 1/(m+1)`.
            let source = d.lemma(p.regular, &[x, n, m]);
            let source_quantity = rsub(d, rat, xn, xm);
            let source_bound = modulus(d, p, n, m);
            let swap_quantity = {
                let forward = d.lemma(rat.sub_neg_sub, &[xm, xn]);
                rsymm(d, goal_quantity, source_quantity, forward)
            };
            let left_atom = div_succ(d, p, 1, n);
            let right_atom = div_succ(d, p, 1, m);
            let swap_bound = d.lemma(rat.add_comm, &[left_atom, right_atom]);
            let at_quantity = rat_eq_rewrite(
                d,
                source_quantity,
                goal_quantity,
                swap_quantity,
                source,
                &|d, t| within(d, p, t, source_bound),
            );
            let moved = rat_eq_rewrite(
                d,
                source_bound,
                goal_bound,
                swap_bound,
                at_quantity,
                &|d, t| within(d, p, goal_quantity, t),
            );
            let over_n = d.lam_fv(n_fv, nat, moved);
            d.lam_fv(m_fv, nat, over_n)
        };
        let constructor = d.kernel().const_(p.mk, vec![]);
        let body = d.apply(constructor, &[representative, regularity]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = d.arrow(carrier, carrier);
        let _ = sequences;
        d.kernel().add_declaration(Declaration::Definition {
            name: p.neg,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 5),
        })?;
    }

    // neg_congr : Equiv x y → Equiv (neg x) (neg y).
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hypothesis = equiv(d, p, x, y);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let a = sample(d, p, x, n);
        let b = sample(d, p, y, n);
        let forward = rsub(d, rat, a, b);
        let bound = div_succ(d, p, 2, n);
        let instance = d.apply(h, &[n]);
        let (lower, upper) = halves(d, p, forward, bound, instance);
        let flipped = d.lemma(rat.bounds_neg, &[forward, bound, lower, upper]);
        let negated_forward = rneg(d, forward);
        let negated_a = rneg(d, a);
        let negated_b = rneg(d, b);
        let target = rsub(d, rat, negated_a, negated_b);
        // `−(a − b) = b − a = (−a) − (−b)`.
        let swapped = rsub(d, rat, b, a);
        let first = d.lemma(rat.neg_sub, &[a, b]);
        let second = {
            let forward_eq = d.lemma(rat.sub_neg_sub, &[a, b]);
            rsymm(d, target, swapped, forward_eq)
        };
        let (_, chained) = rchain(d, negated_forward, &[(swapped, first), (target, second)]);
        let body = rat_eq_rewrite(d, negated_forward, target, chained, flipped, &|d, t| {
            within(d, p, t, bound)
        });
        let _ = rle;
        let value = {
            let over_n = d.lam_fv(n_fv, nat, body);
            let with_h = d.lam_fv(h_fv, hypothesis, over_n);
            let with_y = d.lam_fv(y_fv, carrier, with_h);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let left = d.const_app(p.neg, &[x]);
            let right = d.const_app(p.neg, &[y]);
            let conclusion = equiv(d, p, left, right);
            let inner = d.arrow(hypothesis, conclusion);
            let with_y = d.pi_fv(y_fv, carrier, inner);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.neg_congr,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `2·n + 1`, Bishop's shifted sampling index.
fn shift(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let two = d.num(2);
    let doubled = NatOps::mul(d, two, n);
    d.succ(doubled)
}

/// `CReal.add`, and its `Equiv`-congruence.
///
/// Regularity is the whole content. `f m − f n` splits into the two component
/// errors by `Rat.sub_add_add`, each is bounded by `regular`, and the four
/// resulting summands sort into `(A+A) + (B+B) = 2/(2m+2) + 2/(2n+2)`, which
/// `Rat.natDivSucc_halve` turns into exactly `1/(m+1) + 1/(n+1)`.
fn declare_addition(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    // add x y := mk (fun n => x_{2n+1} + y_{2n+1}) _
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let representative = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let index = shift(d, n);
            let left = sample(d, p, x, index);
            let right = sample(d, p, y, index);
            let body = radd(d, left, right);
            d.lam_fv(n_fv, nat, body)
        };
        let regularity = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let sm = shift(d, m);
            let sn = shift(d, n);
            let a = sample(d, p, x, sm);
            let b = sample(d, p, y, sm);
            let c = sample(d, p, x, sn);
            let e = sample(d, p, y, sn);

            let wx = d.lemma(p.regular, &[x, sm, sn]);
            let wy = d.lemma(p.regular, &[y, sm, sn]);
            let dx = rsub(d, rat, a, c);
            let dy = rsub(d, rat, b, e);
            let component = modulus(d, p, sm, sn);
            let (lx, rx) = halves(d, p, dx, component, wx);
            let (ly, ry) = halves(d, p, dy, component, wy);
            let combined = d.lemma(
                rat.bounds_add,
                &[dx, component, dy, component, lx, rx, ly, ry],
            );
            let summed_quantity = radd(d, dx, dy);
            let summed_bound = radd(d, component, component);

            // The quantity: (a+b) − (c+e) = (a−c) + (b−e).
            let left_sum = radd(d, a, b);
            let right_sum = radd(d, c, e);
            let goal_quantity = rsub(d, rat, left_sum, right_sum);
            let split = d.lemma(rat.sub_add_add, &[a, b, c, e]);
            let back = rsymm(d, goal_quantity, summed_quantity, split);
            let at_quantity = rat_eq_rewrite(
                d,
                summed_quantity,
                goal_quantity,
                back,
                combined,
                &|d, t| within(d, p, t, summed_bound),
            );

            // The bound: (A+B) + (A+B) = (A+A) + (B+B) = 2/(2m+2) + 2/(2n+2)
            //                          = 1/(m+1) + 1/(n+1).
            let a_atom = div_succ(d, p, 1, sm);
            let b_atom = div_succ(d, p, 1, sn);
            let flat_atoms = [a_atom, b_atom, a_atom, b_atom];
            let sorted_atoms = [a_atom, a_atom, b_atom, b_atom];
            let flatten = rsum_append(d, rat, &flat_atoms[..2], &flat_atoms[2..]);
            let flat = rsum(d, rat, &flat_atoms);
            let permute = rsum_perm(d, rat, &flat_atoms, &sorted_atoms);
            let sorted = rsum(d, rat, &sorted_atoms);
            let paired = {
                let forward = rsum_append(d, rat, &sorted_atoms[..2], &sorted_atoms[2..]);
                let doubled_a = radd(d, a_atom, a_atom);
                let doubled_b = radd(d, b_atom, b_atom);
                let target = radd(d, doubled_a, doubled_b);
                rsymm(d, target, sorted, forward)
            };
            let doubled_a = radd(d, a_atom, a_atom);
            let doubled_b = radd(d, b_atom, b_atom);
            let pair_target = radd(d, doubled_a, doubled_b);
            let one_nat = d.num(1);
            let two_a = div_succ(d, p, 2, sm);
            let two_b = div_succ(d, p, 2, sn);
            let fuse_a = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, sm]);
            let fuse_b = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, sn]);
            let after_a = rcongr(d, doubled_a, two_a, fuse_a, &|d, t| radd(d, t, doubled_b));
            let staged_a = radd(d, two_a, doubled_b);
            let after_b = rcongr(d, doubled_b, two_b, fuse_b, &|d, t| radd(d, two_a, t));
            let staged_b = radd(d, two_a, two_b);
            let halve_m = d.lemma(rat.nat_div_succ_halve, &[m]);
            let halve_n = d.lemma(rat.nat_div_succ_halve, &[n]);
            let one_m = div_succ(d, p, 1, m);
            let one_n = div_succ(d, p, 1, n);
            let after_halve_m = rcongr(d, two_a, one_m, halve_m, &|d, t| radd(d, t, two_b));
            let staged_halve = radd(d, one_m, two_b);
            let after_halve_n = rcongr(d, two_b, one_n, halve_n, &|d, t| radd(d, one_m, t));
            let goal_bound = modulus(d, p, m, n);
            let (_, bound_chain) = rchain(
                d,
                summed_bound,
                &[
                    (flat, flatten),
                    (sorted, permute),
                    (pair_target, paired),
                    (staged_a, after_a),
                    (staged_b, after_b),
                    (staged_halve, after_halve_m),
                    (goal_bound, after_halve_n),
                ],
            );
            let moved = rat_eq_rewrite(
                d,
                summed_bound,
                goal_bound,
                bound_chain,
                at_quantity,
                &|d, t| within(d, p, goal_quantity, t),
            );
            let over_n = d.lam_fv(n_fv, nat, moved);
            d.lam_fv(m_fv, nat, over_n)
        };
        let constructor = d.kernel().const_(p.mk, vec![]);
        let body = d.apply(constructor, &[representative, regularity]);
        let value = {
            let with_y = d.lam_fv(y_fv, carrier, body);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let inner = d.arrow(carrier, carrier);
            d.arrow(carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.add,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 6),
        })?;
    }

    // add_congr : Equiv x x' → Equiv y y' → Equiv (add x y) (add x' y').
    //
    // The two component bounds are `2/(2n+2)` each, and `2/(2n+2) = 1/(n+1)`,
    // so their sum is `2/(n+1)` exactly — no slack, and no weakening lemma.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let x2_fv = d.fresh_fvar();
        let x2 = d.kernel().fvar(x2_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let y2_fv = d.fresh_fvar();
        let y2 = d.kernel().fvar(y2_fv);
        let first_ty = equiv(d, p, x, x2);
        let second_ty = equiv(d, p, y, y2);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let index = shift(d, n);
        let a = sample(d, p, x, index);
        let b = sample(d, p, y, index);
        let c = sample(d, p, x2, index);
        let e = sample(d, p, y2, index);
        let dx = rsub(d, rat, a, c);
        let dy = rsub(d, rat, b, e);
        let component = div_succ(d, p, 2, index);
        let wx = d.apply(h1, &[index]);
        let wy = d.apply(h2, &[index]);
        let (lx, rx) = halves(d, p, dx, component, wx);
        let (ly, ry) = halves(d, p, dy, component, wy);
        let combined = d.lemma(
            rat.bounds_add,
            &[dx, component, dy, component, lx, rx, ly, ry],
        );
        let summed_quantity = radd(d, dx, dy);
        let summed_bound = radd(d, component, component);

        let left_sum = radd(d, a, b);
        let right_sum = radd(d, c, e);
        let goal_quantity = rsub(d, rat, left_sum, right_sum);
        let split = d.lemma(rat.sub_add_add, &[a, b, c, e]);
        let back = rsymm(d, goal_quantity, summed_quantity, split);
        let at_quantity = rat_eq_rewrite(
            d,
            summed_quantity,
            goal_quantity,
            back,
            combined,
            &|d, t| within(d, p, t, summed_bound),
        );

        // `2/(2n+2) + 2/(2n+2) = 1/(n+1) + 1/(n+1) = 2/(n+1)`.
        let halved = div_succ(d, p, 1, n);
        let halve = d.lemma(rat.nat_div_succ_halve, &[n]);
        let after_left = rcongr(d, component, halved, halve, &|d, t| radd(d, t, component));
        let staged = radd(d, halved, component);
        let after_right = rcongr(d, component, halved, halve, &|d, t| radd(d, halved, t));
        let doubled = radd(d, halved, halved);
        let one_nat = d.num(1);
        let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
        let goal_bound = div_succ(d, p, 2, n);
        let (_, bound_chain) = rchain(
            d,
            summed_bound,
            &[
                (staged, after_left),
                (doubled, after_right),
                (goal_bound, fuse),
            ],
        );
        let body = rat_eq_rewrite(
            d,
            summed_bound,
            goal_bound,
            bound_chain,
            at_quantity,
            &|d, t| within(d, p, goal_quantity, t),
        );
        let value = {
            let over_n = d.lam_fv(n_fv, nat, body);
            let with2 = d.lam_fv(h2_fv, second_ty, over_n);
            let with1 = d.lam_fv(h1_fv, first_ty, with2);
            let with_y2 = d.lam_fv(y2_fv, carrier, with1);
            let with_y = d.lam_fv(y_fv, carrier, with_y2);
            let with_x2 = d.lam_fv(x2_fv, carrier, with_y);
            d.lam_fv(x_fv, carrier, with_x2)
        };
        let ty = {
            let left = d.const_app(p.add, &[x, y]);
            let right = d.const_app(p.add, &[x2, y2]);
            let conclusion = equiv(d, p, left, right);
            let after2 = d.arrow(second_ty, conclusion);
            let after1 = d.arrow(first_ty, after2);
            let with_y2 = d.pi_fv(y2_fv, carrier, after1);
            let with_y = d.pi_fv(y_fv, carrier, with_y2);
            let with_x2 = d.pi_fv(x2_fv, carrier, with_y);
            d.pi_fv(x_fv, carrier, with_x2)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_congr,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// The **additive group**, in `Equiv` form: four of the 22 ordered-ring laws.
///
/// Two of them are *pointwise* — `add_comm` and `add_neg` sample both sides at
/// the same shifted index, so [`Equiv.of_pointwise`](CRealPrelude::equiv_of_pointwise)
/// reduces each to one `Rat` law and there is no analysis at all.
///
/// The other two are not, and they are where the setoid starts to earn its
/// keep. `add x zero` samples `x` at `2n+1` where `x` itself samples at `n`,
/// and `(x+y)+z` samples `x` at `2(2n+1)+1` where `x+(y+z)` samples it at
/// `2n+1` — so the two sides are equal at *no* index, and only `Equiv` can
/// relate them. Both reduce to regularity plus one inequality,
/// [`shifted_bound_le`], and in `add_assoc` the middle summand `y` is sampled
/// at the same index on both sides and cancels, leaving exactly two regularity
/// bounds. Neither needs `natDivSucc` to be monotone in its index.
fn declare_additive_laws(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    // add_comm : Equiv (add x y) (add y x).
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let left = d.const_app(p.add, &[x, y]);
        let right = d.const_app(p.add, &[y, x]);
        let pointwise = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let index = shift(d, n);
            let a = sample(d, p, x, index);
            let b = sample(d, p, y, index);
            let body = d.lemma(rat.add_comm, &[a, b]);
            d.lam_fv(n_fv, nat, body)
        };
        let body = d.lemma(p.equiv_of_pointwise, &[left, right, pointwise]);
        let value = {
            let with_y = d.lam_fv(y_fv, carrier, body);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let conclusion = equiv(d, p, left, right);
            let with_y = d.pi_fv(y_fv, carrier, conclusion);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_comm,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // add_neg : Equiv (add x (neg x)) zero.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let negated = d.const_app(p.neg, &[x]);
        let left = d.const_app(p.add, &[x, negated]);
        let right = d.kernel().const_(p.zero, vec![]);
        let pointwise = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let index = shift(d, n);
            let a = sample(d, p, x, index);
            let body = d.lemma(rat.add_neg, &[a]);
            d.lam_fv(n_fv, nat, body)
        };
        let body = d.lemma(p.equiv_of_pointwise, &[left, right, pointwise]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let conclusion = equiv(d, p, left, right);
            d.pi_fv(x_fv, carrier, conclusion)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_neg,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // add_zero : Equiv (add x zero) x.
    //
    // The first law that is NOT pointwise. `(x + 0)_n` is `x_{2n+1} + 0`, and
    // `x_n` is `x_n`: the two sides disagree at every index, and regularity is
    // what says the disagreement is small. It bounds the gap by
    // `1/(2n+2) + 1/(n+1)` where the setoid asks for `2/(n+1)`, and
    // `shifted_bound_le` is the whole difference.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let zero_real = d.kernel().const_(p.zero, vec![]);
        let left = d.const_app(p.add, &[x, zero_real]);
        let body = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let index = shift(d, n);
            let deep = sample(d, p, x, index);
            let shallow = sample(d, p, x, n);
            let difference = rsub(d, rat, deep, shallow);
            let bound = modulus(d, p, index, n);
            let goal_bound = div_succ(d, p, 2, n);
            let source = d.lemma(p.regular, &[x, index, n]);
            let order = shifted_bound_le(d, p, n);
            let widened = weaken(d, p, difference, bound, goal_bound, source, order);

            // `x_{2n+1}` is what the left side samples; `x_{2n+1} + 0` is what
            // it *writes*, because `CReal.zero` contributes a `Rat.zero`.
            let zero_rat = rzero(d, rat);
            let padded = radd(d, deep, zero_rat);
            let collapse = d.lemma(rat.add_zero, &[deep]);
            let restore = rsymm(d, padded, deep, collapse);
            let at_index = rat_eq_rewrite(d, deep, padded, restore, widened, &|d, t| {
                let quantity = rsub(d, rat, t, shallow);
                within(d, p, quantity, goal_bound)
            });
            d.lam_fv(n_fv, nat, at_index)
        };
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let conclusion = equiv(d, p, left, x);
            d.pi_fv(x_fv, carrier, conclusion)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // add_assoc : Equiv (add (add x y) z) (add x (add y z)).
    //
    // Write `N = 2n+1` and `M = 2N+1`. The left side samples
    // `(x_M + y_M) + z_N`, the right `x_N + (y_M + z_M)`: `y` is sampled at the
    // SAME index on both sides and cancels, and the whole difference is
    // `(x_M − x_N) + (z_N − z_M)` — two regularity bounds. Their sum is
    // `2/(M+1) + 2/(N+1)`, which halves twice into `1/(N+1) + 1/(n+1)`, the
    // same quantity `add_zero` weakens.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let inner_left = d.const_app(p.add, &[x, y]);
        let left = d.const_app(p.add, &[inner_left, z]);
        let inner_right = d.const_app(p.add, &[y, z]);
        let right = d.const_app(p.add, &[x, inner_right]);
        let body = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let shallow_index = shift(d, n);
            let deep_index = shift(d, shallow_index);
            let xm = sample(d, p, x, deep_index);
            let ym = sample(d, p, y, deep_index);
            let zn = sample(d, p, z, shallow_index);
            let xn = sample(d, p, x, shallow_index);
            let zm = sample(d, p, z, deep_index);

            // The two regularity bounds, added.
            let dx = rsub(d, rat, xm, xn);
            let dz = rsub(d, rat, zn, zm);
            let bx = modulus(d, p, deep_index, shallow_index);
            let bz = modulus(d, p, shallow_index, deep_index);
            let wx = d.lemma(p.regular, &[x, deep_index, shallow_index]);
            let wz = d.lemma(p.regular, &[z, shallow_index, deep_index]);
            let (lx, rx) = halves(d, p, dx, bx, wx);
            let (lz, rz) = halves(d, p, dz, bz, wz);
            let combined = d.lemma(rat.bounds_add, &[dx, bx, dz, bz, lx, rx, lz, rz]);
            let summed_quantity = radd(d, dx, dz);
            let summed_bound = radd(d, bx, bz);

            // The bound: `(A+B) + (B+A) = (A+A) + (B+B) = 2/(M+1) + 2/(N+1)`,
            // and each doubling halves back one level — `2/(M+1) = 1/(N+1)`
            // and `2/(N+1) = 1/(n+1)`.
            let a_deep = div_succ(d, p, 1, deep_index);
            let a_shallow = div_succ(d, p, 1, shallow_index);
            let flat_atoms = [a_deep, a_shallow, a_shallow, a_deep];
            let sorted_atoms = [a_deep, a_deep, a_shallow, a_shallow];
            let flatten = rsum_append(d, rat, &flat_atoms[..2], &flat_atoms[2..]);
            let flat = rsum(d, rat, &flat_atoms);
            let permute = rsum_perm(d, rat, &flat_atoms, &sorted_atoms);
            let sorted = rsum(d, rat, &sorted_atoms);
            let doubled_deep = radd(d, a_deep, a_deep);
            let doubled_shallow = radd(d, a_shallow, a_shallow);
            let pair_target = radd(d, doubled_deep, doubled_shallow);
            let paired = {
                let forward = rsum_append(d, rat, &sorted_atoms[..2], &sorted_atoms[2..]);
                rsymm(d, pair_target, sorted, forward)
            };
            let one_nat = d.num(1);
            let two_deep = div_succ(d, p, 2, deep_index);
            let two_shallow = div_succ(d, p, 2, shallow_index);
            let a_flat = div_succ(d, p, 1, n);
            let fuse_deep = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, deep_index]);
            let after_deep = rcongr(d, doubled_deep, two_deep, fuse_deep, &|d, t| {
                radd(d, t, doubled_shallow)
            });
            let staged_deep = radd(d, two_deep, doubled_shallow);
            let halve_deep = d.lemma(rat.nat_div_succ_halve, &[shallow_index]);
            let after_halve_deep = rcongr(d, two_deep, a_shallow, halve_deep, &|d, t| {
                radd(d, t, doubled_shallow)
            });
            let staged_halved = radd(d, a_shallow, doubled_shallow);
            let fuse_shallow = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, shallow_index]);
            let after_shallow = rcongr(d, doubled_shallow, two_shallow, fuse_shallow, &|d, t| {
                radd(d, a_shallow, t)
            });
            let staged_shallow = radd(d, a_shallow, two_shallow);
            let halve_shallow = d.lemma(rat.nat_div_succ_halve, &[n]);
            let after_halve_shallow = rcongr(d, two_shallow, a_flat, halve_shallow, &|d, t| {
                radd(d, a_shallow, t)
            });
            let regularity_bound = modulus(d, p, shallow_index, n);
            let (_, bound_chain) = rchain(
                d,
                summed_bound,
                &[
                    (flat, flatten),
                    (sorted, permute),
                    (pair_target, paired),
                    (staged_deep, after_deep),
                    (staged_halved, after_halve_deep),
                    (staged_shallow, after_shallow),
                    (regularity_bound, after_halve_shallow),
                ],
            );
            let at_regularity = rat_eq_rewrite(
                d,
                summed_bound,
                regularity_bound,
                bound_chain,
                combined,
                &|d, t| within(d, p, summed_quantity, t),
            );
            let goal_bound = div_succ(d, p, 2, n);
            let order = shifted_bound_le(d, p, n);
            let widened = weaken(
                d,
                p,
                summed_quantity,
                regularity_bound,
                goal_bound,
                at_regularity,
                order,
            );

            // The quantity, in the `add`/`neg` form `Rat.sub` unfolds to:
            // `((x_M + y_M) + z_N) − (x_N + (y_M + z_M))` is six summands, of
            // which `y_M` and `−y_M` cancel.
            let neg_xn = rneg(d, xn);
            let neg_ym = rneg(d, ym);
            let neg_zm = rneg(d, zm);
            let lhs_sum = {
                let inner = radd(d, xm, ym);
                radd(d, inner, zn)
            };
            let rhs_inner = radd(d, ym, zm);
            let rhs_sum = radd(d, xn, rhs_inner);
            let neg_rhs = rneg(d, rhs_sum);
            let quantity = radd(d, lhs_sum, neg_rhs);
            let target = {
                let first = radd(d, xm, neg_xn);
                let second = radd(d, zn, neg_zm);
                radd(d, first, second)
            };

            let opened_left = rsum(d, rat, &[xm, ym, zn]);
            let assoc = d.lemma(rat.add_assoc, &[xm, ym, zn]);
            let step_assoc = rcongr(d, lhs_sum, opened_left, assoc, &|d, t| radd(d, t, neg_rhs));
            let staged_assoc = radd(d, opened_left, neg_rhs);
            let neg_inner = rneg(d, rhs_inner);
            let spread = d.lemma(rat.neg_add, &[xn, rhs_inner]);
            let spread_target = radd(d, neg_xn, neg_inner);
            let step_spread = rcongr(d, neg_rhs, spread_target, spread, &|d, t| {
                radd(d, opened_left, t)
            });
            let staged_spread = radd(d, opened_left, spread_target);
            let spread_inner = d.lemma(rat.neg_add, &[ym, zm]);
            let neg_pair = radd(d, neg_ym, neg_zm);
            let step_inner = rcongr(d, neg_inner, neg_pair, spread_inner, &|d, t| {
                let inner = radd(d, neg_xn, t);
                radd(d, opened_left, inner)
            });
            let opened_right = rsum(d, rat, &[neg_xn, neg_ym, neg_zm]);
            let staged_inner = radd(d, opened_left, opened_right);
            let six_atoms = [xm, ym, zn, neg_xn, neg_ym, neg_zm];
            let joined = rsum_append(d, rat, &six_atoms[..3], &six_atoms[3..]);
            let six = rsum(d, rat, &six_atoms);
            let sorted_six = [xm, neg_xn, zn, neg_zm, ym, neg_ym];
            let permute_six = rsum_perm(d, rat, &six_atoms, &sorted_six);
            let arranged = rsum(d, rat, &sorted_six);
            let zero_rat = rzero(d, rat);
            let pair_ym = radd(d, ym, neg_ym);
            let cancel = d.lemma(rat.add_neg, &[ym]);
            let step_cancel = rcongr(d, pair_ym, zero_rat, cancel, &|d, t| {
                let level1 = radd(d, neg_zm, t);
                let level2 = radd(d, zn, level1);
                let level3 = radd(d, neg_xn, level2);
                radd(d, xm, level3)
            });
            let cancelled = {
                let level1 = radd(d, neg_zm, zero_rat);
                let level2 = radd(d, zn, level1);
                let level3 = radd(d, neg_xn, level2);
                radd(d, xm, level3)
            };
            let padded_tail = radd(d, neg_zm, zero_rat);
            let trim = d.lemma(rat.add_zero, &[neg_zm]);
            let step_trim = rcongr(d, padded_tail, neg_zm, trim, &|d, t| {
                let level2 = radd(d, zn, t);
                let level3 = radd(d, neg_xn, level2);
                radd(d, xm, level3)
            });
            let four_atoms = [xm, neg_xn, zn, neg_zm];
            let four = rsum(d, rat, &four_atoms);
            let fold = {
                let forward = rsum_append(d, rat, &four_atoms[..2], &four_atoms[2..]);
                rsymm(d, target, four, forward)
            };
            let (_, quantity_chain) = rchain(
                d,
                quantity,
                &[
                    (staged_assoc, step_assoc),
                    (staged_spread, step_spread),
                    (staged_inner, step_inner),
                    (six, joined),
                    (arranged, permute_six),
                    (cancelled, step_cancel),
                    (four, step_trim),
                    (target, fold),
                ],
            );
            let restore = rsymm(d, quantity, target, quantity_chain);
            let at_quantity = rat_eq_rewrite(d, target, quantity, restore, widened, &|d, t| {
                within(d, p, t, goal_bound)
            });
            d.lam_fv(n_fv, nat, at_quantity)
        };
        let value = {
            let with_z = d.lam_fv(z_fv, carrier, body);
            let with_y = d.lam_fv(y_fv, carrier, with_z);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let conclusion = equiv(d, p, left, right);
            let with_z = d.pi_fv(z_fv, carrier, conclusion);
            let with_y = d.pi_fv(y_fv, carrier, with_z);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_assoc,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `CReal.ofRat_add : ∀ a b, Equiv (add (ofRat a) (ofRat b)) (ofRat (Rat.add a b))`
/// — the additive counterpart of [`declare_of_rat_mul`](product::declare_of_rat_mul)'s
/// `of_rat_mul`.
///
/// **Checked against the actual definitions, not assumed.** `add x y` samples
/// at the *shifted* index `2n+1`, not at `n` — but `ofRat q`'s representative
/// is the constant function `fun _ => q`, so `seq (ofRat a) (shift n)` reduces
/// to `a` regardless of what the shift computes to, exactly the way
/// `of_rat_mul`'s module doc puts it: "the embedding is a constant sequence,
/// so the product's index shift never matters". The additive shift is no
/// different, and the proof is `Eq.refl`, same as `of_rat_mul`'s.
fn declare_of_rat_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = rat_ty(d);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let left = embed(d, p, a);
    let right = embed(d, p, b);
    let product = cadd(d, p, left, right);
    let scalar = radd(d, a, b);
    let embedded = embed(d, p, scalar);

    let pointwise = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = rrefl(d, scalar);
        let _ = n;
        d.lam_fv(n_fv, nat, body)
    };
    let body = d.lemma(p.equiv_of_pointwise, &[product, embedded, pointwise]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let claim = equiv(d, p, product, embedded);
        let with_b = d.pi_fv(b_fv, carrier, claim);
        d.pi_fv(a_fv, carrier, with_b)
    };
    let _ = rat;
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_rat_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.ofRat_neg : ∀ a, Equiv (neg (ofRat a)) (ofRat (Rat.neg a))`.
///
/// **Checked, not assumed.** `CReal.neg` takes no index shift at all — its
/// representative is `fun n => Rat.neg (seq x n)` — so `seq (neg (ofRat a)) n`
/// reduces to `Rat.neg a` at *every* `n` with no shift to reconcile, and the
/// proof is `Eq.refl`.
fn declare_of_rat_neg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let embedded_a = embed(d, p, a);
    let product = d.const_app(p.neg, &[embedded_a]);
    let scalar = rneg(d, a);
    let embedded = embed(d, p, scalar);

    let pointwise = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = rrefl(d, scalar);
        let _ = n;
        d.lam_fv(n_fv, nat, body)
    };
    let body = d.lemma(p.equiv_of_pointwise, &[product, embedded, pointwise]);
    let value = d.lam_fv(a_fv, carrier, body);
    let ty = {
        let claim = equiv(d, p, product, embedded);
        d.pi_fv(a_fv, carrier, claim)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_rat_neg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.ofRat_sub : ∀ a b,
/// Equiv (add (ofRat a) (neg (ofRat b))) (ofRat (Rat.sub a b))`.
///
/// **`CReal` has no `sub` of its own — checked, not assumed**: no
/// `CReal.sub` name is interned anywhere in this module, so subtraction is
/// stated the way every other law here states it, as `add x (neg y)`. That
/// combination is exactly what `Rat.sub` itself unfolds to (see
/// `rat_prelude::group::rsub`'s doc comment), so both sides still reduce to
/// the same closed rational at every index and the proof is `Eq.refl`.
fn declare_of_rat_sub(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = rat_ty(d);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let embedded_a = embed(d, p, a);
    let embedded_b = embed(d, p, b);
    let negated_b = d.const_app(p.neg, &[embedded_b]);
    let product = cadd(d, p, embedded_a, negated_b);
    let scalar = rsub(d, rat, a, b);
    let embedded = embed(d, p, scalar);

    let pointwise = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = rrefl(d, scalar);
        let _ = n;
        d.lam_fv(n_fv, nat, body)
    };
    let body = d.lemma(p.equiv_of_pointwise, &[product, embedded, pointwise]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let claim = equiv(d, p, product, embedded);
        let with_b = d.pi_fv(b_fv, carrier, claim);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_rat_sub,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.neg_le_neg : ∀ x y, le x y → le (neg y) (neg x)`.
///
/// Bishop's `le` is already one-sided (`∀ n, seq x n − seq y n ≤ 2/(n+1)`),
/// and `neg` takes no index shift, so this is a single `Rat.sub_neg_sub`
/// rewrite at each index `n`, mirroring [`declare_negation`]'s `neg_congr`
/// proof exactly (same shape, `Rat.le` in place of the two-sided `Within`).
fn declare_neg_le_neg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rle = crate::rat_prelude::ops::rle;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let hypothesis = d.const_app(p.le, &[x, y]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let xn = sample(d, p, x, n);
    let yn = sample(d, p, y, n);
    let bound = div_succ(d, p, 2, n);
    let hn = d.apply(h, &[n]);
    let u = rsub(d, rat, xn, yn);
    let negated_y = rneg(d, yn);
    let negated_x = rneg(d, xn);
    let v = rsub(d, rat, negated_y, negated_x);
    let eq_vu = d.lemma(rat.sub_neg_sub, &[yn, xn]);
    let eq_uv = rsymm(d, v, u, eq_vu);
    let moved = rat_eq_rewrite(d, u, v, eq_uv, hn, &|d, t| rle(d, rat, t, bound));
    let value = {
        let over_n = d.lam_fv(n_fv, nat, moved);
        let with_h = d.lam_fv(h_fv, hypothesis, over_n);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let neg_y = d.const_app(p.neg, &[y]);
        let neg_x = d.const_app(p.neg, &[x]);
        let conclusion = d.const_app(p.le, &[neg_y, neg_x]);
        let inner = d.arrow(hypothesis, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.neg_le_neg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.le`, Bishop's order, and the three of the 22 order laws that do not
/// mention multiplication.
///
/// **These three restate verbatim**, which the additive laws did not: none of
/// `le_refl`, `le_trans`, `add_le_add` mentions `Eq`, so there is no equality
/// to replace by `Equiv` and the `AxReal` package's statement is the statement
/// proved here. That is ADR-0512's Measurement 2, cashed.
///
/// The order is *not* decidable and `le_total` is deliberately absent: it holds
/// for `ℚ`, and `∀ x y, le x y ∨ le y x` over the reals is not constructively
/// provable. Nothing here needs it — the one place a classical development
/// would say "suppose not" is `le_trans`, and that is a case split on nothing:
/// the estimate holds for every index `j`, and the Archimedean property of `ℚ`
/// turns "for every `j`" into the bound.
fn declare_order(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rle = crate::rat_prelude::ops::rle;

    // le x y := ∀ n, Rat.le (seq x n − seq y n) (2/(n+1)).
    {
        let prop = d.kernel().sort_zero();
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let left = sample(d, p, x, n);
        let right = sample(d, p, y, n);
        let difference = rsub(d, rat, left, right);
        let bound = div_succ(d, p, 2, n);
        let claim = rle(d, rat, difference, bound);
        let body = d.pi_fv(n_fv, nat, claim);
        let value = {
            let with_y = d.lam_fv(y_fv, carrier, body);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let inner = d.arrow(carrier, prop);
            d.arrow(carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.le,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 7),
        })?;
    }

    // le_refl : le x x. `x_n − x_n = 0`, and `0 ≤ 2/(n+1)`.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let point = sample(d, p, x, n);
            let difference = rsub(d, rat, point, point);
            let bound = div_succ(d, p, 2, n);
            let zero = rzero(d, rat);
            let collapse = d.lemma(rat.sub_self, &[point]);
            let restore = rsymm(d, difference, zero, collapse);
            let two = d.num(2);
            let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
            let at_index = rat_eq_rewrite(d, zero, difference, restore, nonneg, &|d, t| {
                rle(d, rat, t, bound)
            });
            d.lam_fv(n_fv, nat, at_index)
        };
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let conclusion = d.const_app(p.le, &[x, x]);
            d.pi_fv(x_fv, carrier, conclusion)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.le_refl,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // le_trans : le x y → le y z → le x z.
    //
    // Chaining the two hypotheses at `n` gives `x_n − z_n ≤ 4/(n+1)`, which is
    // not what the order asks for and no rearrangement fixes. Bishop compares
    // at an arbitrary third index `j` instead, where the two hypotheses cost
    // `2/(j+1)` each and regularity pays the two round trips, and the
    // Archimedean property of `ℚ` discharges the resulting `6/(j+1)`. This is
    // `Equiv.trans` with the lower half deleted.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let first_ty = d.const_app(p.le, &[x, y]);
        let second_ty = d.const_app(p.le, &[y, z]);
        let hxy_fv = d.fresh_fvar();
        let hxy = d.kernel().fvar(hxy_fv);
        let hyz_fv = d.fresh_fvar();
        let hyz = d.kernel().fvar(hyz_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let head = sample(d, p, x, n);
        let tail = sample(d, p, z, n);
        let target = rsub(d, rat, head, tail);
        let goal_bound = div_succ(d, p, 2, n);

        let hypothesis = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let xj = sample(d, p, x, j);
            let yj = sample(d, p, y, j);
            let zj = sample(d, p, z, j);
            let u1 = rsub(d, rat, head, xj);
            let u2 = rsub(d, rat, xj, yj);
            let u3 = rsub(d, rat, yj, zj);
            let u4 = rsub(d, rat, zj, tail);
            let b1 = modulus(d, p, n, j);
            let b2 = div_succ(d, p, 2, j);
            let b3 = div_succ(d, p, 2, j);
            let b4 = modulus(d, p, j, n);

            // Only the UPPER half of each regularity bound is read; the two
            // hypotheses are one-sided already.
            let w1 = d.lemma(p.regular, &[x, n, j]);
            let w4 = d.lemma(p.regular, &[z, j, n]);
            let (_, r1) = halves(d, p, u1, b1, w1);
            let r2 = d.apply(hxy, &[j]);
            let r3 = d.apply(hyz, &[j]);
            let (_, r4) = halves(d, p, u4, b4, w4);

            // Right-nested, so the quantities telescope in the same order.
            let s34 = d.lemma(rat.add_le_add, &[u3, b3, u4, b4, r3, r4]);
            let q34 = radd(d, u3, u4);
            let c34 = radd(d, b3, b4);
            let s234 = d.lemma(rat.add_le_add, &[u2, b2, q34, c34, r2, s34]);
            let q234 = radd(d, u2, q34);
            let c234 = radd(d, b2, c34);
            let s1234 = d.lemma(rat.add_le_add, &[u1, b1, q234, c234, r1, s234]);
            let q1234 = radd(d, u1, q234);
            let c1234 = radd(d, b1, c234);

            let (_, _, quantity) = telescope_four(d, p, head, xj, yj, zj, tail);
            let (_, final_bound, bound_chain) = six_term_bound(d, p, n, j);
            let at_quantity = rat_eq_rewrite(d, q1234, target, quantity, s1234, &|d, t| {
                rle(d, rat, t, c1234)
            });
            let moved = rat_eq_rewrite(d, c1234, final_bound, bound_chain, at_quantity, &|d, t| {
                rle(d, rat, target, t)
            });
            d.lam_fv(j_fv, nat, moved)
        };
        let six_nat = d.num(6);
        let at_index = d.lemma(
            rat.le_of_le_add_nat_div_succ,
            &[target, goal_bound, six_nat, hypothesis],
        );
        let value = {
            let over_n = d.lam_fv(n_fv, nat, at_index);
            let with_second = d.lam_fv(hyz_fv, second_ty, over_n);
            let with_first = d.lam_fv(hxy_fv, first_ty, with_second);
            let with_z = d.lam_fv(z_fv, carrier, with_first);
            let with_y = d.lam_fv(y_fv, carrier, with_z);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let conclusion = d.const_app(p.le, &[x, z]);
            let after_second = d.arrow(second_ty, conclusion);
            let after_first = d.arrow(first_ty, after_second);
            let with_z = d.pi_fv(z_fv, carrier, after_first);
            let with_y = d.pi_fv(y_fv, carrier, with_z);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.le_trans,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // add_le_add : le x x' → le y y' → le (add x y) (add x' y').
    //
    // Exact, like `add_congr`: both hypotheses are read at the shifted index
    // `2n+1` where each costs `2/(2n+2)`, and `2/(2n+2) = 1/(n+1)`, so the two
    // together are `2/(n+1)` with no slack and no weakening.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let x2_fv = d.fresh_fvar();
        let x2 = d.kernel().fvar(x2_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let y2_fv = d.fresh_fvar();
        let y2 = d.kernel().fvar(y2_fv);
        let first_ty = d.const_app(p.le, &[x, x2]);
        let second_ty = d.const_app(p.le, &[y, y2]);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let index = shift(d, n);
        let a = sample(d, p, x, index);
        let b = sample(d, p, y, index);
        let c = sample(d, p, x2, index);
        let e = sample(d, p, y2, index);
        let dx = rsub(d, rat, a, c);
        let dy = rsub(d, rat, b, e);
        let component = div_succ(d, p, 2, index);
        let wx = d.apply(h1, &[index]);
        let wy = d.apply(h2, &[index]);
        let combined = d.lemma(rat.add_le_add, &[dx, component, dy, component, wx, wy]);
        let summed_quantity = radd(d, dx, dy);
        let summed_bound = radd(d, component, component);

        let left_sum = radd(d, a, b);
        let right_sum = radd(d, c, e);
        let goal_quantity = rsub(d, rat, left_sum, right_sum);
        let split = d.lemma(rat.sub_add_add, &[a, b, c, e]);
        let restore = rsymm(d, goal_quantity, summed_quantity, split);
        let at_quantity = rat_eq_rewrite(
            d,
            summed_quantity,
            goal_quantity,
            restore,
            combined,
            &|d, t| rle(d, rat, t, summed_bound),
        );

        // `2/(2n+2) + 2/(2n+2) = 1/(n+1) + 1/(n+1) = 2/(n+1)`.
        let halved = div_succ(d, p, 1, n);
        let halve = d.lemma(rat.nat_div_succ_halve, &[n]);
        let after_left = rcongr(d, component, halved, halve, &|d, t| radd(d, t, component));
        let staged = radd(d, halved, component);
        let after_right = rcongr(d, component, halved, halve, &|d, t| radd(d, halved, t));
        let doubled = radd(d, halved, halved);
        let one_nat = d.num(1);
        let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
        let goal_bound = div_succ(d, p, 2, n);
        let (_, bound_chain) = rchain(
            d,
            summed_bound,
            &[
                (staged, after_left),
                (doubled, after_right),
                (goal_bound, fuse),
            ],
        );
        let at_index = rat_eq_rewrite(
            d,
            summed_bound,
            goal_bound,
            bound_chain,
            at_quantity,
            &|d, t| rle(d, rat, goal_quantity, t),
        );
        let value = {
            let over_n = d.lam_fv(n_fv, nat, at_index);
            let with2 = d.lam_fv(h2_fv, second_ty, over_n);
            let with1 = d.lam_fv(h1_fv, first_ty, with2);
            let with_y2 = d.lam_fv(y2_fv, carrier, with1);
            let with_y = d.lam_fv(y_fv, carrier, with_y2);
            let with_x2 = d.lam_fv(x2_fv, carrier, with_y);
            d.lam_fv(x_fv, carrier, with_x2)
        };
        let ty = {
            let left = d.const_app(p.add, &[x, y]);
            let right = d.const_app(p.add, &[x2, y2]);
            let conclusion = d.const_app(p.le, &[left, right]);
            let after2 = d.arrow(second_ty, conclusion);
            let after1 = d.arrow(first_ty, after2);
            let with_y2 = d.pi_fv(y2_fv, carrier, after1);
            let with_y = d.pi_fv(y_fv, carrier, with_y2);
            let with_x2 = d.pi_fv(x2_fv, carrier, with_y);
            d.pi_fv(x_fv, carrier, with_x2)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.add_le_add,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // le_of_equiv : Equiv x y → le x y, and equiv_of_le_le : the converse from
    // both directions.
    //
    // Together these say `le` is the order OF this setoid: `Equiv` is the
    // two-sided bound, `le` its upper half, and having both halves is having
    // `Equiv` back. Without them "three order laws hold" is a statement about
    // an unexamined relation — a `le` weakened to `≤ 100/(n+1)` satisfies all
    // three and closes neither of these.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let a = sample(d, p, x, n);
        let b = sample(d, p, y, n);
        let forward = rsub(d, rat, a, b);
        let backward = rsub(d, rat, b, a);
        let bound = div_succ(d, p, 2, n);
        let negated = rneg(d, bound);

        // le_of_equiv: the upper half of the two-sided bound, projected.
        {
            let hypothesis = equiv(d, p, x, y);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let instance = d.apply(h, &[n]);
            let (_, upper) = halves(d, p, forward, bound, instance);
            let value = {
                let over_n = d.lam_fv(n_fv, nat, upper);
                let with_h = d.lam_fv(h_fv, hypothesis, over_n);
                let with_y = d.lam_fv(y_fv, carrier, with_h);
                d.lam_fv(x_fv, carrier, with_y)
            };
            let ty = {
                let conclusion = d.const_app(p.le, &[x, y]);
                let inner = d.arrow(hypothesis, conclusion);
                let with_y = d.pi_fv(y_fv, carrier, inner);
                d.pi_fv(x_fv, carrier, with_y)
            };
            d.kernel().add_declaration(Declaration::Theorem {
                name: p.le_of_equiv,
                uparams: vec![],
                ty,
                value,
            })?;
        }

        // equiv_of_le_le: the second hypothesis, negated, IS the lower half —
        // `−(y_n − x_n) = x_n − y_n` by `Rat.neg_sub`.
        {
            let first_ty = d.const_app(p.le, &[x, y]);
            let second_ty = d.const_app(p.le, &[y, x]);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let upper = d.apply(h1, &[n]);
            let reverse = d.apply(h2, &[n]);
            let flipped = d.lemma(rat.neg_le_neg, &[backward, bound, reverse]);
            let negated_backward = rneg(d, backward);
            let rewrite = d.lemma(rat.neg_sub, &[b, a]);
            let lower = rat_eq_rewrite(d, negated_backward, forward, rewrite, flipped, &|d, t| {
                rle(d, rat, negated, t)
            });
            let lower_ty = rle(d, rat, negated, forward);
            let upper_ty = rle(d, rat, forward, bound);
            let pair = and_intro(d, p, lower_ty, upper_ty, lower, upper);
            let value = {
                let over_n = d.lam_fv(n_fv, nat, pair);
                let with2 = d.lam_fv(h2_fv, second_ty, over_n);
                let with1 = d.lam_fv(h1_fv, first_ty, with2);
                let with_y = d.lam_fv(y_fv, carrier, with1);
                d.lam_fv(x_fv, carrier, with_y)
            };
            let ty = {
                let conclusion = equiv(d, p, x, y);
                let after2 = d.arrow(second_ty, conclusion);
                let after1 = d.arrow(first_ty, after2);
                let with_y = d.pi_fv(y_fv, carrier, after1);
                d.pi_fv(x_fv, carrier, with_y)
            };
            d.kernel().add_declaration(Declaration::Theorem {
                name: p.equiv_of_le_le,
                uparams: vec![],
                ty,
                value,
            })?;
        }
    }

    // not_le_one_zero : Not (le one zero) — the order discriminates.
    //
    // At index `3` the hypothesis says `1 − 0 ≤ 2/4`, i.e. `1 ≤ 1/2`. Every
    // term in that is closed, so `Rat.le` unfolds through `Int.le` to
    // `Nat.le 2 1` by pure reduction, and two Nat lemmas finish it.
    {
        let nat_p = rat.int.nat;
        let one_real = d.kernel().const_(p.one, vec![]);
        let zero_real = d.kernel().const_(p.zero, vec![]);
        let claim = d.const_app(p.le, &[one_real, zero_real]);
        let stmt = d.not(claim);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let index = d.num(3);
        let instance = d.apply(h, &[index]);
        let one_nat = d.num(1);
        let zero_nat = d.zero();
        let stripped = d.lemma(nat_p.le_of_succ_le_succ, &[one_nat, zero_nat, instance]);
        let absurd = d.lemma(nat_p.not_succ_le_zero, &[zero_nat, stripped]);
        let value = d.lam_fv(h_fv, claim, absurd);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.not_le_one_zero,
            uparams: vec![],
            ty: stmt,
            value,
        })?;
    }
    Ok(())
}

// --- the strict order -------------------------------------------------------

/// `CReal.le x y`.
fn cle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.le, &[x, y])
}

/// `CReal.add x y`.
fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

/// `CReal.ofRat q`.
fn embed(d: &mut IntDev<'_>, p: CRealPrelude, q: ExprId) -> ExprId {
    d.const_app(p.of_rat, &[q])
}

/// `CReal.lt x y`.
fn clt(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.lt, &[x, y])
}

/// `λ (q : Rat), And (Rat.lt 0 q) (CReal.le (CReal.add x (CReal.ofRat q)) y)` —
/// the body `CReal.lt` existentially quantifies.
fn gap_predicate(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let rat = p.rat;
    let carrier = rat_ty(d);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let zero = rzero(d, rat);
    let positive = rlt(d, rat, zero, q);
    let embedded = embed(d, p, q);
    let shifted = cadd(d, p, x, embedded);
    let bounded = cle(d, p, shifted, y);
    let body = d.and(positive, bounded);
    d.lam_fv(q_fv, carrier, body)
}

/// `Exists.intro` at [`gap_predicate`]: the rational `q` and a proof of
/// `0 < q ∧ x + q ≤ y` make `CReal.lt x y`.
fn gap_intro(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    q: ExprId,
    proof: ExprId,
) -> ExprId {
    let carrier = rat_ty(d);
    let one = d.level_one();
    let predicate = gap_predicate(d, p, x, y);
    let name = p.rat.int.logic.exists_intro;
    let intro = d.kernel().const_(name, vec![one]);
    d.apply(intro, &[carrier, predicate, q, proof])
}

/// `Exists.rec` at [`gap_predicate`]: consume a `CReal.lt x y` into `target`,
/// given `minor : ∀ (q : Rat), (0 < q ∧ x + q ≤ y) → target`.
///
/// `Exists` is a `Prop` with one non-subsingleton constructor, so the motive
/// must land in `Prop` — which every use here does, the strict-order laws being
/// `Prop`s and `lt_irrefl`'s target being `False`.
fn gap_elim(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let carrier = rat_ty(d);
    let one = d.level_one();
    let predicate = gap_predicate(d, p, x, y);
    let exists_name = p.rat.int.logic.exists_;
    let exists = d.kernel().const_(exists_name, vec![one]);
    let exists_ty = d.apply(exists, &[carrier, predicate]);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, exists_ty, target)
    };
    let rec_name = p.rat.int.logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[carrier, predicate, motive, minor, witness])
}

/// The two halves of a `0 < q ∧ x + q ≤ y` hypothesis, at the shape
/// [`gap_predicate`] gives it.
fn gap_halves(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    q: ExprId,
    proof: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let zero = rzero(d, rat);
    let positive = rlt(d, rat, zero, q);
    let embedded = embed(d, p, q);
    let shifted = cadd(d, p, x, embedded);
    let bounded = cle(d, p, shifted, y);
    let left = d.and_left(positive, bounded, proof);
    let right = d.and_right(positive, bounded, proof);
    (left, right)
}

/// `1/(n+1) + 1/(2n+2) ≤ 2/(n+1)` — [`shifted_bound_le`] with its two summands
/// the other way round, which is the orientation `CReal.regular x n (2n+1)`
/// hands over.
fn shifted_bound_le_comm(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let rat = p.rat;
    let s = shift(d, n);
    let one_n = div_succ(d, p, 1, n);
    let one_s = div_succ(d, p, 1, s);
    let two_n = div_succ(d, p, 2, n);
    let core = shifted_bound_le(d, p, n);
    let swap = d.lemma(rat.add_comm, &[one_s, one_n]);
    let from = radd(d, one_s, one_n);
    let to = radd(d, one_n, one_s);
    rat_eq_rewrite(d, from, to, swap, core, &|d, t| rle(d, rat, t, two_n))
}

/// `Eq Rat (Rat.sub a Rat.zero) a`.
///
/// `Rat.sub a b` is *defined* as `a + (−b)`, so this is `neg_zero` under a
/// congruence and then `add_zero`; there is no `Rat.sub_zero` because nothing
/// before the strict order needed one.
fn sub_zero_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let rat = p.rat;
    let zero = rzero(d, rat);
    let start = rsub(d, rat, a, zero);
    let negated = rneg(d, zero);
    let collapse = d.lemma(rat.neg_zero, &[]);
    let inner = rcongr(d, negated, zero, collapse, &|d, t| radd(d, a, t));
    let padded = radd(d, a, zero);
    let trim = d.lemma(rat.add_zero, &[a]);
    let (_, proof) = rchain(d, start, &[(padded, inner), (a, trim)]);
    proof
}

/// `Eq Rat (Rat.sub (Rat.add a q) a) q` — the cancellation `lt_irrefl` needs to
/// read a bound on `(x_s + q) − x_s` as a bound on `q` itself.
fn add_sub_cancel_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, q: ExprId) -> ExprId {
    let rat = p.rat;
    let zero = rzero(d, rat);
    let sum = radd(d, a, q);
    let start = rsub(d, rat, sum, a);
    let padded = radd(d, a, zero);
    let mid = rsub(d, rat, sum, padded);
    let trim = d.lemma(rat.add_zero, &[a]);
    let forward = rcongr(d, padded, a, trim, &|d, t| rsub(d, rat, sum, t));
    let restore = rsymm(d, mid, start, forward);
    let split = d.lemma(rat.sub_add_add, &[a, q, a, zero]);
    let self_sub = rsub(d, rat, a, a);
    let shifted = rsub(d, rat, q, zero);
    let decomposed = radd(d, self_sub, shifted);
    let vanish = d.lemma(rat.sub_self, &[a]);
    let head = rcongr(d, self_sub, zero, vanish, &|d, t| radd(d, t, shifted));
    let headless = radd(d, zero, shifted);
    let tail = sub_zero_eq(d, p, q);
    let tailless = radd(d, zero, q);
    let cleaned = rcongr(d, shifted, q, tail, &|d, t| radd(d, zero, t));
    let unpad = d.lemma(rat.zero_add, &[q]);
    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid, restore),
            (decomposed, split),
            (headless, head),
            (tailless, cleaned),
            (q, unpad),
        ],
    );
    proof
}

/// `CReal.le_add_of_nonneg`, `CReal.lt`, the seven strict-order laws and the two
/// relation congruences the setoid telescope's equality slot asks for.
fn declare_strict_order(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_le_add_of_nonneg(d, p)?;
    declare_lt(d, p)?;
    declare_lt_laws(d, p)?;
    declare_relation_congruences(d, p)
}

/// `le_add_of_nonneg : ∀ x q, 0 ≤ q → le x (add x (ofRat q))`.
///
/// The one analytic step behind `le_of_lt` and `lt_trans`, and it is analytic
/// because of the index shift: `add x (ofRat q)` samples `x` at `2n+1` where
/// `x` samples it at `n`, so even at `q = 0` the two sides are not equal at any
/// index. Regularity closes the gap and the slack is [`shifted_bound_le`]
/// again — the same inequality `add_zero` and `add_assoc` reduce to.
fn declare_le_add_of_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let zero = rzero(d, rat);
    let hypothesis = rle(d, rat, zero, q);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let s = shift(d, n);
    let near = sample(d, p, x, n);
    let deep = sample(d, p, x, s);
    let displaced = radd(d, deep, q);
    let goal_quantity = rsub(d, rat, near, displaced);
    let two_n = div_succ(d, p, 2, n);

    // `x_n − (x_s + q) = (x_n + 0) − (x_s + q) = (x_n − x_s) + (0 − q)`.
    let padded = radd(d, near, zero);
    let staged = rsub(d, rat, padded, displaced);
    let trim = d.lemma(rat.add_zero, &[near]);
    let forward = rcongr(d, padded, near, trim, &|d, t| rsub(d, rat, t, displaced));
    let restore = rsymm(d, staged, goal_quantity, forward);
    let split = d.lemma(rat.sub_add_add, &[near, zero, deep, q]);
    let drift = rsub(d, rat, near, deep);
    let offset = rsub(d, rat, zero, q);
    let decomposed = radd(d, drift, offset);
    let (_, to_decomposed) = rchain(d, goal_quantity, &[(staged, restore), (decomposed, split)]);

    // `x_n − x_s ≤ 1/(n+1) + 1/(2n+2) ≤ 2/(n+1)`.
    let regularity = d.lemma(p.regular, &[x, n, s]);
    let drift_bound = modulus(d, p, n, s);
    let (_, drift_upper) = halves(d, p, drift, drift_bound, regularity);
    let shrink = shifted_bound_le_comm(d, p, n);
    let drift_bounded = d.lemma(
        rat.le_trans,
        &[drift, drift_bound, two_n, drift_upper, shrink],
    );

    // `0 − q = −q ≤ 0`.
    let negated = rneg(d, q);
    let nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[q, h]);
    let unfolded = d.lemma(rat.zero_add, &[negated]);
    let back = rsymm(d, offset, negated, unfolded);
    let offset_nonpos = rat_eq_rewrite(d, negated, offset, back, nonpos, &|d, t| {
        rle(d, rat, t, zero)
    });

    let combined = d.lemma(
        rat.add_le_add,
        &[drift, two_n, offset, zero, drift_bounded, offset_nonpos],
    );
    let loose_bound = radd(d, two_n, zero);
    let tighten = d.lemma(rat.add_zero, &[two_n]);
    let at_bound = rat_eq_rewrite(d, loose_bound, two_n, tighten, combined, &|d, t| {
        rle(d, rat, decomposed, t)
    });
    let rewind = rsymm(d, goal_quantity, decomposed, to_decomposed);
    let at_index = rat_eq_rewrite(d, decomposed, goal_quantity, rewind, at_bound, &|d, t| {
        rle(d, rat, t, two_n)
    });

    let value = {
        let over_n = d.lam_fv(n_fv, nat, at_index);
        let with_h = d.lam_fv(h_fv, hypothesis, over_n);
        let with_q = d.lam_fv(q_fv, rat_carrier, with_h);
        d.lam_fv(x_fv, carrier, with_q)
    };
    let ty = {
        let embedded = embed(d, p, q);
        let shifted = cadd(d, p, x, embedded);
        let conclusion = cle(d, p, x, shifted);
        let inner = d.arrow(hypothesis, conclusion);
        let with_q = d.pi_fv(q_fv, rat_carrier, inner);
        d.pi_fv(x_fv, carrier, with_q)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.le_add_of_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.lt x y := ∃ (q : Rat), 0 < q ∧ le (add x (ofRat q)) y`.
fn declare_lt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let predicate = gap_predicate(d, p, x, y);
    let exists_name = p.rat.int.logic.exists_;
    let exists = d.kernel().const_(exists_name, vec![one]);
    let body = d.apply(exists, &[rat_carrier, predicate]);
    let value = {
        let with_y = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let inner = d.arrow(carrier, prop);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.lt,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 8),
    })
}

/// The seven ordered-ring laws that mention `lt`.
fn declare_lt_laws(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_le_of_lt(d, p)?;
    declare_lt_trans(d, p)?;
    declare_lt_mixed(d, p)?;
    declare_add_lt_add(d, p)?;
    declare_zero_lt_one(d, p)?;
    declare_lt_irrefl(d, p)
}

/// `le_of_lt : ∀ x y, lt x y → le x y` — the direction a `lt := Not (le y x)`
/// definition could not have supplied constructively, and the reason this one
/// is an `Exists` of a rational gap rather than a negation.
fn declare_le_of_lt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let zero = rzero(d, rat);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let hypothesis = clt(d, p, x, y);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let target = cle(d, p, x, y);

    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let positive = rlt(d, rat, zero, q);
        let embedded = embed(d, p, q);
        let shifted = cadd(d, p, x, embedded);
        let bounded = cle(d, p, shifted, y);
        let witness_ty = d.and(positive, bounded);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let (strict, holds) = gap_halves(d, p, x, y, q, w);
        let nonneg = d.lemma(rat.le_of_lt, &[zero, q, strict]);
        let step = d.lemma(p.le_add_of_nonneg, &[x, q, nonneg]);
        let body = d.lemma(p.le_trans, &[x, shifted, y, step, holds]);
        let with_w = d.lam_fv(w_fv, witness_ty, body);
        d.lam_fv(q_fv, rat_carrier, with_w)
    };
    let body = gap_elim(d, p, x, y, target, h, minor);
    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let inner = d.arrow(hypothesis, target);
        let with_y = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.le_of_lt,
        uparams: vec![],
        ty,
        value,
    })
}

/// `lt_trans : ∀ x y z, lt x y → lt y z → lt x z`.
///
/// **This is the law the naive definition fails**, and the reason it succeeds
/// here is that the gap is carried explicitly: `x + q₁ ≤ y` survives verbatim
/// as the witness for `x < z`, and the second hypothesis is only ever used
/// through `le_of_lt`. A definition reading `∃ n, y_n − x_n > 2/(n+1)` instead
/// has to *recompute* an index for the composite, and the two regularity round
/// trips it takes to move from `n` to that index consume exactly the margin the
/// two hypotheses supply.
fn declare_lt_trans(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let zero = rzero(d, rat);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let first_ty = clt(d, p, x, y);
    let second_ty = clt(d, p, y, z);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let target = clt(d, p, x, z);

    // `lt y z → le y z`, once, outside the first elimination.
    let weakened = d.lemma(p.le_of_lt, &[y, z, h2]);

    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let positive = rlt(d, rat, zero, q);
        let embedded = embed(d, p, q);
        let shifted = cadd(d, p, x, embedded);
        let bounded = cle(d, p, shifted, y);
        let witness_ty = d.and(positive, bounded);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let (strict, holds) = gap_halves(d, p, x, y, q, w);
        let chained = d.lemma(p.le_trans, &[shifted, y, z, holds, weakened]);
        let reached = cle(d, p, shifted, z);
        let pair = and_intro(d, p, positive, reached, strict, chained);
        let body = gap_intro(d, p, x, z, q, pair);
        let with_w = d.lam_fv(w_fv, witness_ty, body);
        d.lam_fv(q_fv, rat_carrier, with_w)
    };
    let body = gap_elim(d, p, x, y, target, h1, minor);
    let value = {
        let with2 = d.lam_fv(h2_fv, second_ty, body);
        let with1 = d.lam_fv(h1_fv, first_ty, with2);
        let with_z = d.lam_fv(z_fv, carrier, with1);
        let with_y = d.lam_fv(y_fv, carrier, with_z);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let after2 = d.arrow(second_ty, target);
        let after1 = d.arrow(first_ty, after2);
        let with_z = d.pi_fv(z_fv, carrier, after1);
        let with_y = d.pi_fv(y_fv, carrier, with_z);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.lt_trans,
        uparams: vec![],
        ty,
        value,
    })
}

/// `lt_of_lt_of_le` and `lt_of_le_of_lt` — the two mixed transitivities.
///
/// The first keeps the gap and extends the right end by `le_trans`; the second
/// has to move the gap across the left end, which is `add_le_add` against
/// `le_refl` at the embedded rational. Neither needs a new estimate.
fn declare_lt_mixed(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let zero = rzero(d, rat);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let target = clt(d, p, x, z);

    // lt_of_lt_of_le : lt x y → le y z → lt x z.
    {
        let first_ty = clt(d, p, x, y);
        let second_ty = cle(d, p, y, z);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let minor = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let positive = rlt(d, rat, zero, q);
            let embedded = embed(d, p, q);
            let shifted = cadd(d, p, x, embedded);
            let bounded = cle(d, p, shifted, y);
            let witness_ty = d.and(positive, bounded);
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let (strict, holds) = gap_halves(d, p, x, y, q, w);
            let chained = d.lemma(p.le_trans, &[shifted, y, z, holds, h2]);
            let reached = cle(d, p, shifted, z);
            let pair = and_intro(d, p, positive, reached, strict, chained);
            let body = gap_intro(d, p, x, z, q, pair);
            let with_w = d.lam_fv(w_fv, witness_ty, body);
            d.lam_fv(q_fv, rat_carrier, with_w)
        };
        let body = gap_elim(d, p, x, y, target, h1, minor);
        let value = {
            let with2 = d.lam_fv(h2_fv, second_ty, body);
            let with1 = d.lam_fv(h1_fv, first_ty, with2);
            let with_z = d.lam_fv(z_fv, carrier, with1);
            let with_y = d.lam_fv(y_fv, carrier, with_z);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let after2 = d.arrow(second_ty, target);
            let after1 = d.arrow(first_ty, after2);
            let with_z = d.pi_fv(z_fv, carrier, after1);
            let with_y = d.pi_fv(y_fv, carrier, with_z);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.lt_of_lt_of_le,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // lt_of_le_of_lt : le x y → lt y z → lt x z.
    {
        let first_ty = cle(d, p, x, y);
        let second_ty = clt(d, p, y, z);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let minor = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let positive = rlt(d, rat, zero, q);
            let embedded = embed(d, p, q);
            let from = cadd(d, p, x, embedded);
            let to = cadd(d, p, y, embedded);
            let bounded = cle(d, p, to, z);
            let witness_ty = d.and(positive, bounded);
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let (strict, holds) = gap_halves(d, p, y, z, q, w);
            let stationary = d.lemma(p.le_refl, &[embedded]);
            let moved = d.lemma(p.add_le_add, &[x, y, embedded, embedded, h1, stationary]);
            let chained = d.lemma(p.le_trans, &[from, to, z, moved, holds]);
            let reached = cle(d, p, from, z);
            let pair = and_intro(d, p, positive, reached, strict, chained);
            let body = gap_intro(d, p, x, z, q, pair);
            let with_w = d.lam_fv(w_fv, witness_ty, body);
            d.lam_fv(q_fv, rat_carrier, with_w)
        };
        let body = gap_elim(d, p, y, z, target, h2, minor);
        let value = {
            let with2 = d.lam_fv(h2_fv, second_ty, body);
            let with1 = d.lam_fv(h1_fv, first_ty, with2);
            let with_z = d.lam_fv(z_fv, carrier, with1);
            let with_y = d.lam_fv(y_fv, carrier, with_z);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let after2 = d.arrow(second_ty, target);
            let after1 = d.arrow(first_ty, after2);
            let with_z = d.pi_fv(z_fv, carrier, after1);
            let with_y = d.pi_fv(y_fv, carrier, with_z);
            d.pi_fv(x_fv, carrier, with_y)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.lt_of_le_of_lt,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `add_lt_add_of_le_of_lt : ∀ x y c e, le x y → lt c e → lt (add x c) (add y e)`.
///
/// The gap moves out of the right summand and up to the top of the sum, which
/// is one `add_assoc` — read through `le_of_equiv`, because `add_assoc` holds
/// in `Equiv` form and the order is what has to consume it.
fn declare_add_lt_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let zero = rzero(d, rat);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let first_ty = cle(d, p, x, y);
    let second_ty = clt(d, p, c, e);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let left = cadd(d, p, x, c);
    let right = cadd(d, p, y, e);
    let target = clt(d, p, left, right);

    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let positive = rlt(d, rat, zero, q);
        let embedded = embed(d, p, q);
        let inner = cadd(d, p, c, embedded);
        let bounded = cle(d, p, inner, e);
        let witness_ty = d.and(positive, bounded);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let (strict, holds) = gap_halves(d, p, c, e, q, w);
        let summed = d.lemma(p.add_le_add, &[x, y, inner, e, h1, holds]);
        let nested = cadd(d, p, x, inner);
        let flat = cadd(d, p, left, embedded);
        let regroup = d.lemma(p.add_assoc, &[x, c, embedded]);
        let reassociate = d.lemma(p.le_of_equiv, &[flat, nested, regroup]);
        let chained = d.lemma(p.le_trans, &[flat, nested, right, reassociate, summed]);
        let reached = cle(d, p, flat, right);
        let pair = and_intro(d, p, positive, reached, strict, chained);
        let body = gap_intro(d, p, left, right, q, pair);
        let with_w = d.lam_fv(w_fv, witness_ty, body);
        d.lam_fv(q_fv, rat_carrier, with_w)
    };
    let body = gap_elim(d, p, c, e, target, h2, minor);
    let value = {
        let with2 = d.lam_fv(h2_fv, second_ty, body);
        let with1 = d.lam_fv(h1_fv, first_ty, with2);
        let with_e = d.lam_fv(e_fv, carrier, with1);
        let with_c = d.lam_fv(c_fv, carrier, with_e);
        let with_y = d.lam_fv(y_fv, carrier, with_c);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let after2 = d.arrow(second_ty, target);
        let after1 = d.arrow(first_ty, after2);
        let with_e = d.pi_fv(e_fv, carrier, after1);
        let with_c = d.pi_fv(c_fv, carrier, with_e);
        let with_y = d.pi_fv(y_fv, carrier, with_c);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.add_lt_add_of_le_of_lt,
        uparams: vec![],
        ty,
        value,
    })
}

/// `zero_lt_one : lt zero one` — and the **non-vacuity witness for `lt`**.
///
/// The other six strict-order laws all *consume* a `lt`, so every one of them
/// holds of the empty relation with an empty footprint. This is the only one
/// that produces one, and it produces it by exhibiting the gap `q = 1`: at
/// every index the claim reduces to `(0 + 1) − 1 ≤ 2/(n+1)`, i.e. `0 ≤ 2/(n+1)`.
fn declare_zero_lt_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let zero_rat = rzero(d, rat);
    let one_rat = rone(d, rat);
    let zero_real = d.kernel().const_(p.zero, vec![]);
    let one_real = d.kernel().const_(p.one, vec![]);

    let bounded = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sum = radd(d, zero_rat, one_rat);
        let quantity = rsub(d, rat, sum, one_rat);
        let bound = div_succ(d, p, 2, n);
        let unpad = d.lemma(rat.zero_add, &[one_rat]);
        let step = rcongr(d, sum, one_rat, unpad, &|d, t| rsub(d, rat, t, one_rat));
        let degenerate = rsub(d, rat, one_rat, one_rat);
        let collapse = d.lemma(rat.sub_self, &[one_rat]);
        let (_, to_zero) = rchain(d, quantity, &[(degenerate, step), (zero_rat, collapse)]);
        let back = rsymm(d, quantity, zero_rat, to_zero);
        let two = d.num(2);
        let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
        let at_index = rat_eq_rewrite(d, zero_rat, quantity, back, nonneg, &|d, t| {
            rle(d, rat, t, bound)
        });
        d.lam_fv(n_fv, nat, at_index)
    };
    let positive = rlt(d, rat, zero_rat, one_rat);
    let embedded = embed(d, p, one_rat);
    let shifted = cadd(d, p, zero_real, embedded);
    let reached = cle(d, p, shifted, one_real);
    let strict = d.lemma(rat.zero_lt_one, &[]);
    let pair = and_intro(d, p, positive, reached, strict, bounded);
    let value = gap_intro(d, p, zero_real, one_real, one_rat, pair);
    let ty = clt(d, p, zero_real, one_real);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.zero_lt_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `lt_irrefl : ∀ x, Not (lt x x)` — and the **discrimination witness for
/// `lt`**: with `zero_lt_one` it says the strict order is neither empty nor
/// total.
///
/// The gap `q` is real, so a witness for `x < x` says `x_{2n+1} + q ≤ x_n +
/// 2/(n+1)` at every index. Regularity bounds `x_n − x_{2n+1}` by `2/(n+1)`
/// ([`shifted_bound_le`] again), so `q ≤ 4/(n+1)` for **every** `n` and the
/// Archimedean property of `ℚ` forces `q ≤ 0`, contradicting `0 < q`. There is
/// no double negation anywhere in that: the contradiction is
/// `Rat.lt_irrefl` applied to `Rat.lt_of_lt_of_le`.
fn declare_lt_irrefl(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let nat = d.nat_ty();
    let zero = rzero(d, rat);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hypothesis = clt(d, p, x, x);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let false_ty = d.false_ty();

    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let positive = rlt(d, rat, zero, q);
        let embedded = embed(d, p, q);
        let shifted = cadd(d, p, x, embedded);
        let bounded = cle(d, p, shifted, x);
        let witness_ty = d.and(positive, bounded);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let (strict, holds) = gap_halves(d, p, x, x, q, w);

        let over_n = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let s = shift(d, n);
            let deep = sample(d, p, x, s);
            let near = sample(d, p, x, n);
            let displaced = radd(d, deep, q);
            let forward = rsub(d, rat, displaced, near);
            let backward = rsub(d, rat, near, deep);
            let two_n = div_succ(d, p, 2, n);
            let at_index = d.apply(holds, &[n]);

            let regularity = d.lemma(p.regular, &[x, n, s]);
            let drift_bound = modulus(d, p, n, s);
            let (_, drift_upper) = halves(d, p, backward, drift_bound, regularity);
            let shrink = shifted_bound_le_comm(d, p, n);
            let drift_bounded = d.lemma(
                rat.le_trans,
                &[backward, drift_bound, two_n, drift_upper, shrink],
            );
            let combined = d.lemma(
                rat.add_le_add,
                &[forward, two_n, backward, two_n, at_index, drift_bounded],
            );
            let summed = radd(d, forward, backward);
            let doubled = radd(d, two_n, two_n);

            // `((x_s + q) − x_n) + (x_n − x_s) = (x_s + q) − x_s = q`.
            let telescoped = rsub(d, rat, displaced, deep);
            let fuse = d.lemma(rat.sub_add_sub, &[displaced, near, deep]);
            let at_quantity = rat_eq_rewrite(d, summed, telescoped, fuse, combined, &|d, t| {
                rle(d, rat, t, doubled)
            });
            let cancel = add_sub_cancel_eq(d, p, deep, q);
            let bare = rat_eq_rewrite(d, telescoped, q, cancel, at_quantity, &|d, t| {
                rle(d, rat, t, doubled)
            });

            // `2/(n+1) + 2/(n+1) = 4/(n+1) = 0 + 4/(n+1)`.
            let two_nat = d.num(2);
            let four_n = div_succ(d, p, 4, n);
            let merge = d.lemma(rat.nat_div_succ_add, &[two_nat, two_nat, n]);
            let fused = rat_eq_rewrite(d, doubled, four_n, merge, bare, &|d, t| rle(d, rat, q, t));
            let padded = radd(d, zero, four_n);
            let unpad = d.lemma(rat.zero_add, &[four_n]);
            let repad = rsymm(d, padded, four_n, unpad);
            let shaped = rat_eq_rewrite(d, four_n, padded, repad, fused, &|d, t| rle(d, rat, q, t));
            d.lam_fv(n_fv, nat, shaped)
        };
        let four_nat = d.num(4);
        let vanishes = d.lemma(rat.le_of_le_add_nat_div_succ, &[q, zero, four_nat, over_n]);
        let degenerate = d.lemma(rat.lt_of_lt_of_le, &[zero, q, zero, strict, vanishes]);
        let refutation = d.lemma(rat.lt_irrefl, &[zero]);
        let body = d.apply(refutation, &[degenerate]);
        let with_w = d.lam_fv(w_fv, witness_ty, body);
        d.lam_fv(q_fv, rat_carrier, with_w)
    };
    let body = gap_elim(d, p, x, x, false_ty, h, minor);
    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        d.lam_fv(x_fv, carrier, with_h)
    };
    let ty = {
        let inner = d.not(hypothesis);
        d.pi_fv(x_fv, carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.lt_irrefl,
        uparams: vec![],
        ty,
        value,
    })
}

/// `le_congr` and `lt_congr` — the two relation congruences the setoid
/// telescope's equality slot binds (ADR-0512 phase R3), for the two relations
/// that are not operations.
///
/// Neither is an estimate: `le_congr` is `le_of_equiv` on each side and two
/// `le_trans`, and `lt_congr` moves the *same* rational gap across an
/// `add_congr`. They are here because phase R4 asks for them by name, and
/// because a setoid whose order is not `Equiv`-invariant is not an ordered
/// setoid at all.
fn declare_relation_congruences(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let zero = rzero(d, rat);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let left_ty = equiv(d, p, a, b);
    let right_ty = equiv(d, p, c, e);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hce_fv = d.fresh_fvar();
    let hce = d.kernel().fvar(hce_fv);

    // le_congr : Equiv a b → Equiv c e → le a c → le b e.
    {
        let source = cle(d, p, a, c);
        let conclusion = cle(d, p, b, e);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let reversed = d.lemma(p.equiv_symm, &[a, b, hab]);
        let head = d.lemma(p.le_of_equiv, &[b, a, reversed]);
        let tail = d.lemma(p.le_of_equiv, &[c, e, hce]);
        let first = d.lemma(p.le_trans, &[b, a, c, head, h]);
        let body = d.lemma(p.le_trans, &[b, c, e, first, tail]);
        let value = {
            let with_h = d.lam_fv(h_fv, source, body);
            let with_ce = d.lam_fv(hce_fv, right_ty, with_h);
            let with_ab = d.lam_fv(hab_fv, left_ty, with_ce);
            let with_e = d.lam_fv(e_fv, carrier, with_ab);
            let with_c = d.lam_fv(c_fv, carrier, with_e);
            let with_b = d.lam_fv(b_fv, carrier, with_c);
            d.lam_fv(a_fv, carrier, with_b)
        };
        let ty = {
            let after_source = d.arrow(source, conclusion);
            let after_ce = d.arrow(right_ty, after_source);
            let after_ab = d.arrow(left_ty, after_ce);
            let with_e = d.pi_fv(e_fv, carrier, after_ab);
            let with_c = d.pi_fv(c_fv, carrier, with_e);
            let with_b = d.pi_fv(b_fv, carrier, with_c);
            d.pi_fv(a_fv, carrier, with_b)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.le_congr,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // lt_congr : Equiv a b → Equiv c e → lt a c → lt b e.
    {
        let source = clt(d, p, a, c);
        let conclusion = clt(d, p, b, e);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let reversed = d.lemma(p.equiv_symm, &[a, b, hab]);
        let tail = d.lemma(p.le_of_equiv, &[c, e, hce]);
        let minor = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let positive = rlt(d, rat, zero, q);
            let embedded = embed(d, p, q);
            let from = cadd(d, p, b, embedded);
            let to = cadd(d, p, a, embedded);
            let bounded = cle(d, p, to, c);
            let witness_ty = d.and(positive, bounded);
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let (strict, holds) = gap_halves(d, p, a, c, q, w);
            let stationary = d.lemma(p.equiv_refl, &[embedded]);
            let moved = d.lemma(
                p.add_congr,
                &[b, a, embedded, embedded, reversed, stationary],
            );
            let cast = d.lemma(p.le_of_equiv, &[from, to, moved]);
            let first = d.lemma(p.le_trans, &[from, to, c, cast, holds]);
            let chained = d.lemma(p.le_trans, &[from, c, e, first, tail]);
            let reached = cle(d, p, from, e);
            let pair = and_intro(d, p, positive, reached, strict, chained);
            let body = gap_intro(d, p, b, e, q, pair);
            let with_w = d.lam_fv(w_fv, witness_ty, body);
            d.lam_fv(q_fv, rat_carrier, with_w)
        };
        let body = gap_elim(d, p, a, c, conclusion, h, minor);
        let value = {
            let with_h = d.lam_fv(h_fv, source, body);
            let with_ce = d.lam_fv(hce_fv, right_ty, with_h);
            let with_ab = d.lam_fv(hab_fv, left_ty, with_ce);
            let with_e = d.lam_fv(e_fv, carrier, with_ab);
            let with_c = d.lam_fv(c_fv, carrier, with_e);
            let with_b = d.lam_fv(b_fv, carrier, with_c);
            d.lam_fv(a_fv, carrier, with_b)
        };
        let ty = {
            let after_source = d.arrow(source, conclusion);
            let after_ce = d.arrow(right_ty, after_source);
            let after_ab = d.arrow(left_ty, after_ce);
            let with_e = d.pi_fv(e_fv, carrier, after_ab);
            let with_c = d.pi_fv(c_fv, carrier, with_e);
            let with_b = d.pi_fv(b_fv, carrier, with_c);
            d.pi_fv(a_fv, carrier, with_b)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.lt_congr,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}
