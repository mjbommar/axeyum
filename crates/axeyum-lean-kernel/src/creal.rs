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
use crate::name::{NameId, NameNode};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::{rsub, rsum, rsum_append, rsum_perm};
use crate::rat_prelude::ops::{
    radd, rat_eq_rewrite, rat_ty, rchain, rcongr, rle, rlt, rneg, rone, rrefl, rsymm, rzero,
};
use crate::rat_prelude::{RatPrelude, build_rat_prelude};
use crate::{Kernel, KernelError, PreludeKey, PreludeValue};

pub use completeness::CompletenessNames;
pub use cos_sign::CosSignNames;
pub use crossing::CrossingNames;
pub use deriv_unique::DerivUniqueNames;
pub use evt_row1::EvtRow1Names;
pub use exp_fn::ExpFnNames;
pub use extreme_value::ExtremeValueNames;
pub use inverse_fn::InverseFnNames;
/// Re-exported so `CRealPrelude::ivt_boundary` -- a `pub` field -- has a
/// publicly nameable type. `mod creal` is private at the crate root, so a
/// `pub struct` inside it is not reachable without this; without it the
/// `private_interfaces` lint fires. ADR-1512.
pub use ivt_boundary::IvtBoundaryNames;
pub use lub_boundary::LubBoundaryNames;
pub use mvt::MvtNames;
pub use pi::PiNames;
pub use polynomial::PolynomialNames;
pub use ratio_test::RatioTestNames;

/// The build table the prelude actually runs: `STEP_DISPATCH`'s order and
/// dispatch, plus the `requires`/`provides` edges
/// `scripts/creal-declare-deps.py` measures from this module's source. See
/// [`steps_generated`] for why it is generated rather than written.
use steps_generated::STEPS;

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
    /// `CReal.mul_self_abs : ∀ x, Equiv (mul (abs x) (abs x)) (mul x x)`.
    ///
    /// The **unconditional** half of the constructive triangle-inequality
    /// gap: `sqrt (mul t t) ~ abs t` without a `0 ≤ t` hypothesis on either
    /// side, needed because `Complex.abs_add_le`'s Cauchy–Schwarz cross term
    /// `re z · re w + im z · im w` has no known sign, so
    /// [`Self::le_of_sq_le`] cannot be applied to it directly — the classical
    /// proof's silent trichotomy on a real has no constructive counterpart
    /// (`CReal.le` is undecidable; `Rat.le_or_lt`, a *decidable* order, only
    /// exists one level down, on the representation).
    ///
    /// Same shape as [`Self::neg_mul_neg`], not composable from
    /// `sqrt_le_sqrt`/`sqrt_sq`/`abs_mul`/`le_of_sq_le` (`sqrt_sq` needs
    /// `0 ≤ t` for the identical reason `le_of_sq_le` does): `bound (abs x)`
    /// and `bound x` are provably equal naturals rather than the same
    /// literal (`Rat.abs`/`Rat.max` decide on the sign of an *integer*, so
    /// nothing about `seq (abs x) 0` reduces at a symbolic `x` without a
    /// `Rat.le_or_lt` case split — see
    /// `rat_prelude::abs::abs_num_nat_abs_eq`), which is what lets both
    /// products sample at a value-equal index; the per-index step is
    /// `rat_prelude::abs::mul_self_abs_rat` (`|q|·|q| = q·q`, itself a
    /// `Rat.le_or_lt` case split whose negative branch is
    /// [`Self::neg_mul_neg`]'s `sq_neg_eq` specialised to one variable).
    pub mul_self_abs: NameId,
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
    /// `CReal.inv_nonneg : ∀ x k (h : PosBound x k), le zero (inv x k h)`.
    ///
    /// **The prerequisite `mul_le_mul_of_nonneg_left` needs to cancel a
    /// positive factor**, and nothing simpler substitutes for it: multiplying
    /// through by `inv x k h` needs to know that factor is itself nonnegative,
    /// and no existing law says so. Proved at the representative level, the
    /// same way [`Self::inv`]'s own regularity is: `PosBound x k` gives
    /// `L := 1/(2k+2) ≤ x_{j(n)}` at `inv`'s own sampling index `j(n)`
    /// (`declare_inverse`'s `sample_lower`, reproduced here because it is
    /// private to that module), so `0 < x_{j(n)}` and `Rat.inv_pos` makes the
    /// reciprocal itself nonnegative at every `n` — `CReal.le`'s direct `∀n`
    /// form needs nothing more.
    pub inv_nonneg: NameId,
    /// `CReal.le_of_mul_le_mul_left : ∀ c x y k (h : PosBound c k),
    /// le (mul c x) (mul c y) → le x y` — **cancellation**, with the positive
    /// factor's separating modulus threaded through as data, matching
    /// [`Self::inv`]'s own signature.
    ///
    /// `0 < c` alone is not eliminable into this: `CReal`'s order is
    /// undecidable, `Apart` is a bare `Or`, and there is no Markov principle in
    /// this development. `PosBound c k` is exactly the data `inv` already
    /// needs, so nothing new is assumed by asking for it here too.
    ///
    /// The route multiplies through by `inv c k h` on the left:
    /// `mul_le_mul_of_nonneg_left` (needing [`Self::inv_nonneg`]) turns
    /// `mul c x ≤ mul c y` into `mul inv (mul c x) ≤ mul inv (mul c y)`, and
    /// `mul inv (mul c w) ≈ w` via `mul_assoc`, `mul_comm`, `mul_inv_cancel`
    /// and `mul_one` transports each side back through [`Self::le_congr`].
    pub le_of_mul_le_mul_left: NameId,

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
    /// `CReal.min_mono_left : ∀ x y b, le x y → le (min x b) (min y b)` —
    /// one [`Self::le_trans`] into [`Self::le_min`]. See `creal/lattice.rs`.
    pub min_mono_left: NameId,
    /// `CReal.max_mono_right : ∀ a u v, le u v → le (max a u) (max a v)` —
    /// one [`Self::le_trans`] into [`Self::max_le`]. See `creal/lattice.rs`.
    pub max_mono_right: NameId,
    /// `CReal.clamp_mono : ∀ a b x y, le x y →
    /// le (max a (min x b)) (max a (min y b))`.
    ///
    /// The clamp [`Self::antiderivative`] is built from is **monotone** —
    /// [`Self::min_mono_left`] then [`Self::max_mono_right`]. Needed because
    /// [`Self::has_derivative_on`]'s spec quantifies over an unordered pair
    /// and the two antiderivative values are integrals to the two clamps.
    /// See `creal/lattice.rs`.
    pub clamp_mono: NameId,
    /// `CReal.clamp_id : ∀ a b x, le a x → le x b →
    /// Equiv (max a (min x b)) x` — **the clamp is the identity on its own
    /// interval**.
    ///
    /// [`Self::has_derivative_on`]'s spec quantifies over `x` with
    /// `a ≤ x ≤ b`, and [`Self::antiderivative`]'s value there is an
    /// integral up to `max a (min x b)`; every algebraic step that must see
    /// the raw `x` needs this. Two [`Self::equiv_of_le_le`]s against the
    /// universal properties. See `creal/lattice.rs`.
    pub clamp_id: NameId,
    /// `CReal.max_sub_min : ∀ x y,
    /// Equiv (add (max x y) (neg (min x y))) (abs (add y (neg x)))`.
    ///
    /// **The spread of a pair is the magnitude of its difference**, proved
    /// with no case split: the classical argument decides `x ≤ y`, which
    /// `CReal.le` cannot, and both inequalities are one-sided consequences of
    /// the universal properties instead. The lower bound on the meet — the
    /// direction a meet does not hand you — is [`Self::le_min`]. See
    /// `creal/lattice.rs`.
    pub max_sub_min: NameId,
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
    /// `CReal.abs_add_le : ∀ a b, le (abs (add a b)) (add (abs a) (abs b))` —
    /// the two-term triangle inequality, from [`Self::abs_le`] with
    /// [`Self::add_le_add`]/[`Self::le_abs_self`] for the lower branch and
    /// `neg (add a b) ~ add (neg a) (neg b)` plus [`Self::neg_le_abs`] for the
    /// upper (negated) branch. This statement was proved as a private helper
    /// independently in `creal/series.rs`, `creal/derivative.rs`,
    /// `creal/uniform_continuity.rs` and `creal/deriv_unique.rs` before this
    /// declaration gave it one public name; each private copy is unchanged
    /// and still calls its own file-local proof route.
    pub abs_add_le: NameId,
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
    /// `CReal.neg` or `CReal.abs` — see `density` for why
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
    /// `creal/completeness.rs`'s own 5 names, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.completeness.regular_seq` and documented in
    /// [`CompletenessNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub completeness: CompletenessNames,

    // --- convergence of sequences of `CReal` (ADR-0512 phase R9) -------------
    /// `CReal.Converges (f : Nat → CReal) (L : CReal) : Prop :=
    /// ∃ (K : Nat), ∀ n, Within (seq (f n) n − seq L n) (Rat.natDivSucc K n)`.
    ///
    /// The canonical-sample, free-constant formulation — see
    /// `convergence`'s module documentation for why this
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
    /// `CReal.converges_of_close : ∀ f g L (Kc : Nat), (∀ n, Within (seq (g
    /// n) n − seq (f n) n) (Rat.natDivSucc Kc n)) → Converges f L →
    /// Converges g L`.
    ///
    /// The one-hypothesis, two-SEQUENCE generalization of
    /// [`Self::converges_unique`]'s own `equiv_of_bounded` idiom: rather
    /// than comparing two limits of the SAME sequence, this compares two
    /// DIFFERENT sequences pointwise close at their own shared index `n`
    /// (`g n`'s sample at `n` against `f n`'s sample at `n`, not a common
    /// canonical index) and transports `f`'s convergence to `L` over to
    /// `g`. One `Exists.rec` on the single `Converges f L` hypothesis
    /// (`Converges g L` does not mention its witness), then the plain
    /// forward triangle identity `Rat.sub_add_sub` — `(g_n − f_n) + (f_n −
    /// L_n) = g_n − L_n` — fuses the two rates via `Rat.natDivSucc_add`. No
    /// `Rat.bounds_neg` step, unlike `converges_unique`'s own `L − M`
    /// shape, which needs one term negated first.
    ///
    /// Built for `creal/integral.rs`'s `CReal.integral_witness_independent`:
    /// the cross bridge that lets a Riemann-sum diagonal built from one
    /// uniform-continuity witness inherit convergence to the OTHER
    /// witness's integral value, once the two diagonals are shown
    /// pointwise close.
    pub converges_of_close: NameId,
    /// `CReal.converges_of_const : ∀ c, Converges (fun _ => c) c`.
    pub converges_of_const: NameId,
    /// `CReal.converges_of_equiv : ∀ f target, (∀ n, Equiv (f n) target) →
    /// Converges f target`.
    ///
    /// A sequence EXACTLY `Equiv` to a fixed target at every index (not just
    /// in the limit) `Converges` to it at rate `K := 2` — one instantiation
    /// of `Equiv`'s own per-index bound, no new estimate. See
    /// `convergence.rs`'s `declare_converges_of_equiv` for why this is the
    /// second half of the general bridge `CReal.integral_const` needs.
    pub converges_of_equiv: NameId,
    /// `CReal.Cauchy (f : Nat → CReal) : Prop :=
    /// ∃ (K : Nat), ∀ m n, Within (seq (f m) m − seq (f n) n)
    /// (Rat.natDivSucc K m + Rat.natDivSucc K n)`.
    pub cauchy: NameId,
    /// `CReal.converges_cauchy : ∀ f L, Converges f L → Cauchy f`.
    pub converges_cauchy: NameId,
    /// `CReal.regular_of_scaled_cauchy : ∀ f K,
    /// (∀ m n, Within (seq (f m) m − seq (f n) n)
    ///    (Rat.natDivSucc K m + Rat.natDivSucc K n)) →
    /// Regular (speedup (fun n => seq (f n) n) K)`.
    ///
    /// The `Cauchy → Converges` bridge's reusable half. A `K`-scaled Cauchy
    /// witness is not itself a [`CompletenessNames::regular_seq`] instance: `RegularSeq`'s
    /// fixed modulus has no room for the extra factor `K`. But the **diagonal**
    /// `fun n => seq (f n) n` (a bare `Nat → Rat`, not a `Nat → CReal`) is
    /// exactly [`Self::k_regular_pred`]'s shape at `c := K` — the Cauchy
    /// hypothesis, read at `(m, n)`, *is* `KRegular (diagonal f) K`'s own
    /// bound, up to widening the numerator `K ↦ K+1` by one
    /// `Rat.natDivSucc_le_add_left` step each side — so
    /// [`Self::regular_of_kregular`] applies unchanged and needs no new
    /// estimate. This is **not** the `RegularSeq (X : Nat → CReal)` shape a
    /// first reading of the goal suggests: routing a `Nat → CReal` sequence
    /// through [`CompletenessNames::regular_seq`]/[`CompletenessNames::limit`] forces a
    /// [`Self::regular`] bridge at the *shallow* outer index on top of the
    /// Cauchy estimate, which costs a whole extra `1/(m+1)` per side and
    /// overshoots `RegularSeq`'s fixed modulus by a factor of two — see
    /// `convergence.rs`'s module documentation for the full accounting. Going
    /// through the raw diagonal and [`Self::speedup`] instead has no such
    /// bridge (the speed-up's own sample *is* the diagonal value, not a
    /// resampling of it), and closes exactly.
    pub regular_of_scaled_cauchy: NameId,
    /// `CReal.converges_of_scaled_cauchy : ∀ f K,
    /// (∀ m n, Within (seq (f m) m − seq (f n) n)
    ///    (Rat.natDivSucc K m + Rat.natDivSucc K n)) →
    /// Converges f (CReal.mk (speedup (diagonal f) K)
    ///   (regular_of_scaled_cauchy f K h))`.
    ///
    /// The "speedup transported" bridge, and [`Self::regular_of_scaled_cauchy`]'s
    /// companion: whenever `f` satisfies the SAME `K`-scaled Cauchy estimate
    /// that makes `speedup (diagonal f) K` `Regular`, `f` also `Converges` to
    /// the exact `CReal` that estimate builds via `CReal.mk`. Shares its
    /// whole proof body with [`Self::converges_of_cauchy`]'s own inner
    /// derivation (`speedup_close` plus one `Rat.natDivSucc_add` fusion); the
    /// only difference is that `h`/`K` are bare hypotheses here rather than
    /// an eliminated `Cauchy f` witness, so the conclusion NAMES the
    /// constructed limit instead of hiding it behind an `Exists`. Built for
    /// `creal/integral.rs`'s `CReal.integral_converges`, which ties
    /// `CReal.integral`'s own `mk`/`speedup` construction back to
    /// `Converges` — reusable by any future `integral_*` evaluation law that
    /// needs the same tie.
    pub converges_of_scaled_cauchy: NameId,
    /// `CReal.converges_of_cauchy : ∀ f, Cauchy f →
    /// Exists (fun L => Converges f L)`.
    ///
    /// **The `Cauchy → Converges` bridge.** Eliminates `Cauchy f`'s witness
    /// `K`, builds `L := CReal.mk (speedup (diagonal f) K) (regularity proof)`
    /// via [`Self::regular_of_scaled_cauchy`], and closes `Converges f L`
    /// with [`Self::speedup_close`] (which bounds `f n` against `speedup
    /// (diagonal f) K` at the *same* index `n` — exactly `Converges`'s own
    /// shape) plus one `Rat.natDivSucc_add` fusion of the two-part rate into
    /// a single witness `K+2`. `L` is not named outside the proof (`Cauchy`'s
    /// own `K` is not either), so the conclusion is existential.
    pub converges_of_cauchy: NameId,

    // --- algebra of limits (ADR-0512 phase R9, continued) --------------------
    /// `CReal.converges_add : ∀ f g L M, Converges f L → Converges g M →
    /// Converges (fun n => add (f n) (g n)) (add L M)`.
    ///
    /// The first algebra-of-limits theorem, and the one the previous slice's
    /// blocker was about: `add`'s Bishop shift means `seq (add (f n) (g n)) n`
    /// samples `f n` and `g n` at `shift n`, not at `n`, so each summand needs
    /// bridging through its own regularity before `Converges`'s hypotheses
    /// apply. See `convergence`'s module documentation
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
    /// `CReal.converges_squeeze : ∀ a b c L, (∀ n, le (a n) (b n)) →
    /// (∀ n, le (b n) (c n)) → Converges a L → Converges c L → Converges b L`.
    ///
    /// The squeeze (sandwich) theorem. Unlike [`Self::converges_add`], no
    /// shift bridge is needed: [`Self::le`] is `∀ n, seq x n − seq y n ≤
    /// 2/(n+1)`, the *same* canonical-sample idiom [`Self::converges`] itself
    /// uses, so `(hab n) n` and `(hbc n) n` land directly at the same index
    /// `n` the two `Converges` hypotheses are read at — no third index, no
    /// Archimedean lemma, only `Rat.add_le_add`/`Rat.neg_le_neg` telescoping
    /// and one `Rat.natDivSucc_le_add_left` widening per side to a common
    /// witness `K := (2+K_a)+(2+K_c)`.
    pub converges_squeeze: NameId,
    /// `CReal.converges_lower_bound : ∀ a f L, (∀ n, le a (f n)) →
    /// Converges f L → le a L`.
    ///
    /// A non-strict lower bound on a convergent sequence bounds its limit
    /// below — the "compare at an arbitrary third index" idiom
    /// [`Self::le_trans`] itself uses, routed through `f j` instead of a
    /// second `CReal`. See `creal/convergence.rs`'s own module documentation
    /// for why this (and its mirror [`Self::converges_upper_bound`]) answers
    /// the domain-hypothesis question the (unbuilt, and not provable in the
    /// fixed-rate form the `Converges` predicate states) `converges_comp`
    /// needed.
    pub converges_lower_bound: NameId,
    /// `CReal.converges_lower_bound_shift : ∀ s a f L, (∀ n, le a (f
    /// (Nat.add n s))) → Converges f L → le a L`.
    ///
    /// The EVENTUAL form [`Self::converges_lower_bound`] cannot supply: that
    /// one needs its pointwise bound at literally every `n`, including `n =
    /// 0`, which a bound established only from monotonicity past some point
    /// (e.g. `CReal.e`'s partial sums, zero at `n = 0`) does not have. See
    /// `creal/convergence.rs`'s own doc on the declaration for the shift +
    /// re-weaken telescope.
    pub converges_lower_bound_shift: NameId,
    /// `CReal.converges_upper_bound : ∀ f L b, (∀ n, le (f n) b) →
    /// Converges f L → le L b`. The mirror of
    /// [`Self::converges_lower_bound`].
    pub converges_upper_bound: NameId,
    /// `creal/cos_sign.rs`'s own 6 names, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.cos_sign.converges_upper_bound_shift` and documented in
    /// [`CosSignNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub cos_sign: CosSignNames,
    /// `CReal.converges_le : ∀ f g L M, Converges f L → Converges g M →
    /// (∀ n, le (f n) (g n)) → le L M`.
    ///
    /// Order passes to the limit: built from [`Self::converges_sub`] (giving
    /// `Converges (fun n => add (f n) (neg (g n))) (add L (neg M))`) plus the
    /// pointwise hypothesis rearranged into `∀ n, le (add (f n) (neg (g n)))
    /// zero` via [`Self::add_le_add`]/[`Self::add_neg`], then
    /// [`Self::converges_upper_bound`] against the constant `zero` gives `le
    /// (add L (neg M)) zero`, and one more `add_le_add`/ring-identity
    /// rearrangement (add `M` to both sides, cancel) recovers `le L M`. No new
    /// Riemann-sum or accuracy-index machinery — every step is either an
    /// already-proved `Converges` combinator or ordinary ring/order algebra
    /// over `CReal`.
    pub converges_le: NameId,

    // --- boundedness of sequences, and sequential continuity (phase R10) ----
    /// `CReal.Bounded (g : Nat → CReal) : Prop :=
    /// ∃ (B : Nat), ∀ (n : Nat), Within (seq (g n) n) (Rat.natDivSucc B 0)`.
    ///
    /// The canonical-sample boundedness a product's variable shift needs
    /// (`CReal.mulShift` scales by a bound on each multiplicand — see
    /// `convergence`'s module documentation on
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
    /// re-derived. See `convergence`'s module
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
    /// `CReal.continuous_mul : ∀ F G x, ContinuousAt F x → ContinuousAt G x →
    /// ContinuousAt (fun r => mul (F r) (G r)) x`.
    ///
    /// The product's closure law, transferred from [`Self::converges_mul`]
    /// exactly as [`Self::continuous_add`] transfers
    /// [`Self::converges_add`] — no new rational estimate, only the
    /// substitution `L := F x`, `M := G x`.
    pub continuous_mul: NameId,
    /// `CReal.continuous_comp : ∀ F G x, ContinuousAt F x →
    /// ContinuousAt G (F x) → ContinuousAt (fun r => G (F r)) x`.
    ///
    /// Composition. For `g` converging to `x`, `hF` gives `Converges (fun n
    /// => F (g n)) (F x)`, and applying `hG` to *that* sequence gives
    /// `Converges (fun n => G (F (g n))) (G (F x))` — the target, up to
    /// beta. No rational estimate at all, and no shift bridge: this is a
    /// chain of two existing modulus witnesses, not a new one.
    pub continuous_comp: NameId,

    /// `CReal.converges_comp_eventually : ∀ F a b (u : UniformlyContinuousOn
    /// F a b) f L, (∀ n, le a (f n)) → (∀ n, le (f n) b) → Converges f L →
    /// ∀ e, ∃ N, ∀ n, Nat.le N n → close_within (F (f n)) (F L) (natDivSucc
    /// 1 e)`.
    ///
    /// **The repair for `docs/mathematics-2026-08/diary-exact-root-obstruction.md`'s
    /// refuted `converges_comp`.** The fixed-rate composition (`Converges f
    /// L → UniformlyContinuousOn F a b → Converges (F ∘ f) (F L)`) is FALSE
    /// here: `UniformlyContinuousOn`'s `modulus : Nat → Nat` carries no
    /// growth bound, so composing an `O(1/n)`-convergent sequence through a
    /// √-shaped modulus genuinely converges at `O(1/√n)`, and no fixed `K'`
    /// witnesses a faster rate. This *eventual* form is the true statement:
    /// for each target accuracy `e`, `N := K·(modulus(e)+1)` works, and the
    /// witness is computed by forward evaluation of `modulus` alone — no
    /// `Nat` division or search. Conclusion in `close_within` form (the
    /// shape [`Self::uc_spec`] itself produces), not `Within` (the shape
    /// [`Self::converges`] uses) — the two differ (one is index-tied to a
    /// representative, the other a genuine real-valued bound) and the spec
    /// application is a one-step consumer of exactly `close_within`.
    ///
    /// The domain hypotheses `le a L`/`le L b` are not required separately:
    /// [`Self::converges_lower_bound`]/[`Self::converges_upper_bound`]
    /// derive them from `(∀n, le a (f n))`/`(∀n, le (f n) b)` plus
    /// `Converges f L`.
    pub converges_comp_eventually: NameId,

    // --- uniform continuity on an interval (phase R11) -----------------------
    /// `CReal.UniformlyContinuousOn (F : CReal -> CReal) (a b : CReal) : Type :=
    /// mk (modulus : Nat -> Nat) (spec : ...)`.
    ///
    /// **The modulus is data, not a proof.** [`Self::pos_bound_of_lt`] already
    /// establishes the house rule this follows: `0 < x` and its Nat-indexed
    /// witness are the SAME proposition, yet the witness cannot be pulled out of
    /// the `Exists` and used to build anything in `Type` -- [`Self::inv`] pays
    /// for exactly this by taking its modulus `k : Nat` as an explicit argument
    /// rather than deriving it from a `PosBound` proof. A `Prop`-level `forall
    /// eps, exists delta, ...` has the identical shape and the identical wall: a
    /// later construction (a partition, a sampling index) needs delta as `Nat`
    /// DATA, and `Exists.rec`'s target must not depend on the witness when the
    /// target is a `Type`. So `UniformlyContinuousOn` is declared in `Type`, with
    /// `modulus : Nat -> Nat` a field exactly like [`Self::seq`] is a field of
    /// `CReal` itself, and the ONE-constructor inductive shape (`Type`-valued
    /// data field + `Prop`-valued spec field, large elimination for the first
    /// projection) is copied from `CReal`'s OWN carrier
    /// (`declare_carrier` in this same file), not
    /// invented fresh.
    ///
    /// The spec is real-valued, not the `Converges`/`Cauchy` canonical-sample
    /// idiom this file otherwise prefers: `le (abs (x - y)) (ofRat (1/(modulus
    /// n + 1))) -> le (abs (F x - F y)) (ofRat (1/(n+1)))`. The canonical-sample
    /// form ties "which term" to "which accuracy index" as the SAME `n`, and
    /// every attempt to route a `Converges` witness through it needs the
    /// hypothesis and the conclusion read at two DIFFERENT indices; the
    /// real-valued form is index-free in `x, y` and lets the reader unfold `le`
    /// at whichever sample index the rest of a proof already needs.
    pub uniformly_continuous_on: NameId,
    /// `UniformlyContinuousOn.mk`, the one constructor.
    pub uc_mk: NameId,
    /// `UniformlyContinuousOn.rec`, the kernel-generated recursor (three leading
    /// parameters `F a b`, since -- unlike `CReal` itself -- this family is
    /// genuinely parametric).
    pub uc_rec: NameId,
    /// `UniformlyContinuousOn.modulus : forall F a b, UniformlyContinuousOn F a b
    /// -> Nat -> Nat` -- the data field, by large elimination, exactly
    /// [`Self::seq`]'s own shape one level up.
    pub uc_modulus: NameId,
    /// `UniformlyContinuousOn.spec` -- the Prop-valued field, projected with the
    /// SAME shape [`Self::regular`] uses to project `CReal`'s own Prop field: the
    /// motive at a witness `u` mentions `UniformlyContinuousOn.modulus F a b u`,
    /// not a fresh variable.
    pub uc_spec: NameId,
    /// `CReal.uniformlyContinuousOn_restrict : ∀ F a b a' b',
    /// UniformlyContinuousOn F a b → le a a' → le a' b' → le b' b →
    /// UniformlyContinuousOn F a' b'` (`uniform_continuity::
    /// declare_uniformly_continuous_on_restrict`) -- the sub-interval
    /// restriction `integral_split`'s own assembly needs to turn ONE
    /// witness on `[a,b]` into witnesses on `[a,c]`/`[c,b]`. Built directly
    /// from [`Self::uc_mk`] with the SAME `modulus` field: `a ≤ a' ≤ x`
    /// and `y ≤ b' ≤ b` compose (via [`Self::le_trans`]) to the ORIGINAL
    /// witness's own range hypotheses `a ≤ x`/`y ≤ b`, so its `spec` is
    /// reused verbatim at every `(n, x, y)` -- no new estimate, and no
    /// modulus change.
    pub uniformly_continuous_on_restrict: NameId,
    /// `CReal.uniformly_continuous_id : forall a b, UniformlyContinuousOn (fun r
    /// => r) a b` -- modulus `fun n => n`: the hypothesis IS the conclusion,
    /// verbatim.
    pub uniformly_continuous_id: NameId,
    /// `CReal.uniformly_continuous_const : forall c a b, UniformlyContinuousOn
    /// (fun _ => c) a b` -- any modulus works (`fun _ => 0` is used); `c - c` is
    /// `Equiv`-zero, so the conclusion holds independently of the hypothesis.
    pub uniformly_continuous_const: NameId,
    /// `CReal.uniformly_continuous_add : forall F G a b, UniformlyContinuousOn F
    /// a b -> UniformlyContinuousOn G a b -> UniformlyContinuousOn (fun r => add
    /// (F r) (G r)) a b` -- combined modulus `mF(2n+1) + mG(2n+1)`, the same
    /// shape `creal/derivative.rs`'s `hasDerivative_add` uses for its own
    /// combined modulus, unblocked the same way by
    /// [`Rat.natDivSucc_antitone`](crate::RatPrelude::nat_div_succ_antitone).
    /// See `creal/uniform_continuity.rs`.
    pub uniformly_continuous_add: NameId,
    /// `CReal.uniformly_continuous_neg : ∀ F a b, UniformlyContinuousOn F a b
    /// -> UniformlyContinuousOn (fun r => neg (F r)) a b` -- modulus
    /// UNCHANGED (`mF` itself); `abs (neg _)` costs one `double_neg`/`abs_le`
    /// argument, no new estimate. See `creal/uniform_continuity.rs`.
    pub uniformly_continuous_neg: NameId,
    /// `CReal.uniformly_continuous_sub : ∀ F G a b, UniformlyContinuousOn F a
    /// b -> UniformlyContinuousOn G a b -> UniformlyContinuousOn (fun r =>
    /// add (F r) (neg (G r))) a b` -- pure composition of
    /// [`Self::uniformly_continuous_add`] and [`Self::uniformly_continuous_neg`].
    /// See `creal/uniform_continuity.rs`.
    pub uniformly_continuous_sub: NameId,
    /// `CReal.uniformly_continuous_mul : ∀ F G a b, UniformlyContinuousOn F a
    /// b -> UniformlyContinuousOn G a b -> ∀ k1 k2, BoundedOn F a b k1 ->
    /// BoundedOn G a b k2 -> UniformlyContinuousOn (fun r => mul (F r)
    /// (G r)) a b` -- `|F(x)G(x)-F(y)G(y)| <= |F(x)||G(x)-G(y)| +
    /// |G(y)||F(x)-F(y)|`, each term rescaled by its own `BoundedOn` weight
    /// via `Rat.natDivSucc_scale` and folded back to a single
    /// `1/(2(n+1))` share. See `creal/uniform_continuity.rs`.
    pub uniformly_continuous_mul: NameId,
    /// `CReal.uniformly_continuous_sq : ∀ a b k, BoundedOn (fun r => r) a b k
    /// -> UniformlyContinuousOn (fun r => mul r r) a b` --
    /// [`Self::uniformly_continuous_mul`] at `F := G := id`, both `BoundedOn`
    /// witnesses the SAME hypothesis. See `creal/uniform_continuity.rs`.
    pub uniformly_continuous_sq: NameId,
    /// `CReal.bounded_on_id_unit : BoundedOn (fun r => r) zero (mag_bound 0)
    /// 0` -- `id` bounded by `1` on `[0, mag_bound 0]`, where `mag_bound 0`
    /// IS the kernel's own representation of the real number `1` (chosen so
    /// the proof needs no separate `CReal.one`-vs-`mag_bound` bridge lemma).
    /// See `creal/uniform_continuity.rs`.
    pub bounded_on_id_unit: NameId,
    /// `CReal.bounded_on_id_zero_one : BoundedOn (fun r => r) zero one 0` --
    /// `id` bounded by `1` on `[0, 1]` (the ordinary unit interval, unlike
    /// [`Self::bounded_on_id_unit`]'s `[0, mag_bound 0]`). Built via the
    /// `CReal.one`-vs-`mag_bound 0` bridge
    /// ([`Self::rat_unit_eq_one`]) transporting a range hypothesis `le z
    /// one` into `le z (mag_bound 0)`, then applying
    /// [`Self::bounded_on_id_unit`] directly -- no re-derivation of its own
    /// magnitude argument. See `creal/uniform_continuity.rs`.
    pub bounded_on_id_zero_one: NameId,
    /// `CReal.uniformly_continuous_poly_example : UniformlyContinuousOn (fun
    /// r => add (add (mul r r) r) one) zero (mag_bound 0)` -- `x -> x^2 + x +
    /// 1` uniformly continuous on `[0,1]`, assembled from
    /// [`Self::uniformly_continuous_sq`], [`Self::uniformly_continuous_id`],
    /// [`Self::uniformly_continuous_const`] and
    /// [`Self::uniformly_continuous_add`] with every `BoundedOn` hypothesis
    /// discharged concretely via [`Self::bounded_on_id_unit`]. See
    /// `creal/uniform_continuity.rs`.
    pub uniformly_continuous_poly_example: NameId,
    /// `CReal.mag_bound_le_sum_range_of_lt : ∀ (g : Nat → Nat) (n i : Nat),
    /// Nat.lt i n → CReal.le (mag_bound (g i)) (CReal.sumRange (fun j =>
    /// mag_bound (g j)) n)` — a `Nat`-indexed family of magnitude bounds is
    /// dominated by their running sum, by induction on `n` with no
    /// comparison of `CReal`s (only `Nat.lt`/`Eq Nat` case splits): the
    /// `CReal`-valued analogue of `Nat.le_sumRange_of_lt`
    /// (`nat_prelude/binomial.rs`), needed because `CReal.le` cannot decide
    /// a maximum by comparison but a sum of nonnegatives still dominates
    /// each addend. Declared in a THIRD `uniform_continuity.rs` entry point
    /// (`declare_uniform_continuity_sums`) because it consumes
    /// `CReal.sumRange`, which `series::declare_series` declares after both
    /// of this module's earlier entry points. See
    /// `creal/uniform_continuity.rs`.
    pub mag_bound_le_sum_range_of_lt: NameId,
    /// `CReal.bucketIndex : CReal → Nat → Nat` — the computable "which
    /// sample bucket does `w` fall into" primitive toward
    /// `bounded_of_uniformly_continuous`'s covering argument, given a step
    /// size `1/(Nat.succ k)`.
    ///
    /// ```text
    /// bucketIndex w k :=
    ///   let k1 := Nat.succ k                          -- Nat
    ///   let j  := k1 * k1                              -- Nat, the sample index
    ///   let q  := Rat.max (CReal.seq w j) Rat.zero       -- Rat, clamped >= 0
    ///   let a  := Int.natAbs (Rat.num q)                  -- Nat
    ///   let b  := Rat.den q                                -- Nat, >= 1
    ///   Nat.div (a * k1) b                                  -- Nat
    /// ```
    ///
    /// Verbatim in *recipe* to `creal/sqrt.rs`'s own `sqrtApprox`
    /// (`declare_sqrt_approx`): sample `w` at accuracy index `j = k1²`
    /// (finer than the target resolution `1/k1` by a full factor of `k1`),
    /// clamp to nonnegative via `Rat.max _ Rat.zero` (no case split on `w`'s
    /// sign — `Rat.max` dispatches structurally, and `Rat.le_max_left`/
    /// `Rat.le_max_right` bound both directions with no hypothesis), read
    /// the clamped sample's numerator/denominator as `Nat`s (`Int.natAbs` is
    /// *exact*, not merely an upper bound, precisely because clamping made
    /// the numerator already nonnegative), and floor-divide `numerator *
    /// k1` by the denominator via `Nat.div` — decidable Nat arithmetic
    /// throughout, no comparison of `CReal`s anywhere.
    ///
    /// **Now proved to be within a fixed multiple of one step of `w`**,
    /// in both directions: [`Self::bucket_clamp_upper`] and
    /// [`Self::bucket_clamp_lower`] compose exactly the route this comment
    /// used to defer — `Rat`'s own regularity-sample bound (`w` vs
    /// `CReal.seq w j`) — with [`Self::bucket_index_floor_lower`]/
    /// [`Self::bucket_index_floor_upper`]'s own floor error, still leaving
    /// slack (`2/(j+1)` and `3/(j+1)` respectively, not an exact
    /// nearest-index guarantee) rather than trying to remove it — see this
    /// section's own module documentation in
    /// `creal/uniform_continuity.rs` for why the `2`/`3` slack is fine for
    /// the covering argument this primitive exists for
    /// ([`Self::bounded_of_uniformly_continuous`] — **landed**; this comment
    /// read "not yet landed" long after
    /// `uniform_continuity::declare_bounded_of_uniformly_continuous` became a
    /// `BuildStep`, and a stale absence claim is worse than none, because the
    /// next lane sizes work that is already done. What it then needed, and
    /// [`Self::bucket_index_bound`] now supplies, was a computable `Nat` bound
    /// on `bucketIndex (sub z a) k` uniform over `z ∈ [a,b]`, derived from
    /// `CReal.bound (sub b a)` via `Rat.sub_max_le` + `CReal.bound_within` +
    /// `Rat.max_le` to bound the clamped sample `q` first, then a
    /// cross-multiplication argument inverting `Rat.natDivSucc` back into a
    /// `Nat.le` on `bucketIndex` itself — the same shape
    /// [`Self::bucket_index_floor_lower`]/[`Self::bucket_index_floor_upper`]'s
    /// own proofs use, just in the other direction).
    pub bucket_index: NameId,
    /// `CReal.bucketIndexFloorLower : ∀ w k, Rat.le (Rat.natDivSucc
    /// (CReal.bucketIndex w k) k) (Rat.max (CReal.seq w ((Nat.succ
    /// k)*(Nat.succ k))) Rat.zero)` — the closeness property
    /// [`Self::bucket_index`]'s own doc comment says is missing, in its
    /// sharpest, **hypothesis-free** form: the clamped sample `q := Rat.max
    /// (seq w j) 0` (`j` the exact accuracy index `bucketIndex` itself
    /// samples at) is `>=` the multiple of `1/(k+1)` `bucketIndex w k`
    /// names. No sign hypothesis on `w` is needed — `q >= 0` unconditionally
    /// (`Rat.le_max_right`), which is exactly what makes `a := natAbs (num
    /// q)` an EXACT read of `num q`, not merely a bound. Proved by reading
    /// `Nat.div_mod_bounds`'s lower half (via `Nat.div_mod_exec`, which needs
    /// the divisor written `Nat.succ _`, so `den q` is first rewritten along
    /// `Nat.succ_pred_of_pos`) back into `Rat.le` by cross-multiplying
    /// against `Rat.natDivSucc`'s own `normalize`d representative
    /// (`Rat.normalize_cross`). See `creal/uniform_continuity.rs`.
    pub bucket_index_floor_lower: NameId,
    /// `CReal.bucketIndexFloorUpper : ∀ w k, Rat.le (Rat.max (CReal.seq w
    /// ((Nat.succ k)*(Nat.succ k))) Rat.zero) (Rat.natDivSucc (Nat.succ
    /// (CReal.bucketIndex w k)) k)` — the other half of
    /// [`Self::bucket_index_floor_lower`]: `q` is also `<=` the NEXT
    /// multiple of `1/(k+1)`, from `Nat.div_mod_bounds`'s strict upper half.
    /// Together the two pin `q` inside a single step of `bucketIndex w k`'s
    /// own multiple, which is what the module documentation asks for.
    pub bucket_index_floor_upper: NameId,
    /// `CReal.bucketClampUpper : ∀ w k, CReal.le w (CReal.ofRat (Rat.add
    /// (Rat.max (CReal.seq w ((Nat.succ k)*(Nat.succ k))) Rat.zero)
    /// (Rat.natDivSucc 2 ((Nat.succ k)*(Nat.succ k)))))` — the boundedness
    /// theorem's step 1, upper half: relates the clamped bucket sample `q :=
    /// Rat.max (seq w j) 0` (`j` the accuracy index [`Self::bucket_index`]
    /// itself samples at) back to `w` ITSELF, not merely to `q`. `w` is at
    /// most `q + 2/(j+1)`, via `w`'s own regularity (`seq w n` is within
    /// `1/(n+1)+1/(j+1)` of `seq w j`) plus `seq w j <= q`
    /// (`Rat.le_max_left`, unconditional). **No sign hypothesis on `w` is
    /// needed** — see [`Self::bucket_clamp_lower`] for the half that does.
    /// See `creal/uniform_continuity.rs`.
    pub bucket_clamp_upper: NameId,
    /// `CReal.bucketClampLower : ∀ w k, CReal.le CReal.zero w →
    /// CReal.le (CReal.ofRat (Rat.sub (Rat.max (CReal.seq w ((Nat.succ
    /// k)*(Nat.succ k))) Rat.zero) (Rat.natDivSucc 3 ((Nat.succ
    /// k)*(Nat.succ k))))) w` — the other half of
    /// [`Self::bucket_clamp_upper`]: `w` is at least `q - 3/(j+1)`. **This
    /// is the one place a sign hypothesis on `w` genuinely enters**: without
    /// `le zero w`, `seq w j` could be arbitrarily negative, the clamp to
    /// `0` would then discard an unbounded amount, and no fixed multiple of
    /// `1/(j+1)` would relate `q` back to `w`. With `le zero w`, `seq w j >=
    /// -2/(j+1)`, so the clamp changes it by at most that much, and
    /// `q <= seq w j + 2/(j+1)` unconditionally (`Rat.max_le` on the two
    /// branches `Rat.le_or_lt`-free — actually via `Rat.max_le` applied to
    /// the two bounds `seq w j <= seq w j + 2/(j+1)` and
    /// `0 <= seq w j + 2/(j+1)`, the second using `le zero w` at index
    /// `j`). Combined with `w`'s regularity at `(j,n)` and
    /// `Rat.natDivSucc_add`/`Rat.natDivSucc_le_add_left`, the constant `3`
    /// falls out as `1 (regularity slack) + 2 (the clamp's own slack)`. See
    /// `creal/uniform_continuity.rs`.
    pub bucket_clamp_lower: NameId,
    /// `CReal.bucketIndexBound : ∀ (w bnd : CReal) (k : Nat), CReal.le w bnd →
    /// Nat.le (CReal.bucketIndex w k) (Nat.mul (Nat.add (Nat.succ
    /// (CReal.bound bnd)) 2) (Nat.succ k))` — step 2 toward
    /// `bounded_of_uniformly_continuous`: a COMPUTABLE `Nat` bound on
    /// `bucketIndex w k`, uniform over every `w` known only to satisfy `w ≤
    /// bnd` (no lower bound on `w` needed at all — see below).
    ///
    /// The route is simpler than [`Self::bucket_index_floor_lower`]/
    /// [`Self::bucket_index_floor_upper`]'s own needed: it does **not**
    /// reuse [`Self::bucket_clamp_upper`]/[`Self::bucket_clamp_lower`],
    /// because those relate the clamped sample back to `w`'s own
    /// regularity, which is exactly the chain a bound on `w` alone lets us
    /// skip. Instead the clamped sample `q := Rat.max (seq w j) 0` (`j` the
    /// accuracy index [`Self::bucket_index`] itself samples at) is bounded
    /// directly: `hle` at index `j` gives `seq w j ≤ seq bnd j + 2/(j+1)`
    /// (`Rat.le_of_sub_le`), [`Self::bound_within`] `bnd j` gives `seq bnd j
    /// ≤ (bound bnd + 1)/1`, `2/(j+1) ≤ 2/1` widens via
    /// `Rat.natDivSucc_le_one` applied twice plus `Rat.natDivSucc_add`, and
    /// the two fuse into a single integer bound `C := bound bnd + 3` via
    /// `Rat.natDivSucc_add` again — at which point `Rat.max_le` (using `0 ≤
    /// C` from `Rat.zero_le_natDivSucc`) gives `q ≤ C` with **no sign
    /// hypothesis on `w` anywhere**, unlike the clamp lemmas: clamping to
    /// `≥ 0` only ever needs a sign hypothesis to relate the clamp back
    /// DOWNWARD to `w` (`bucket_clamp_lower`'s own concern), never to bound
    /// it from above.
    ///
    /// The remaining step inverts [`Self::bucket_index_floor_lower`]
    /// (`natDivSucc (bucketIndex w k) k ≤ q`) against `q ≤ C` by
    /// cross-multiplication, the same `Rat.normalize_cross` +
    /// `Rat.int_le_of_mul_le_mul_right` shape
    /// [`Self::bucket_index_floor_lower`]'s own proof uses, run in the
    /// OTHER direction: from a `Rat.le` between two `Rat.normalize`
    /// representatives (one at denominator `k+1`, one at denominator `1`)
    /// to a `Nat.le` on the numerator `bucketIndex w k` itself, scaled by
    /// `k+1`. See `creal/uniform_continuity.rs`.
    pub bucket_index_bound: NameId,
    /// `creal/crossing.rs`'s own 9 names, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.crossing.crossing_index` and documented in
    /// [`CrossingNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub crossing: CrossingNames,
    /// `CReal.sampleUpperBound : ∀ x m, CReal.le x (CReal.ofRat (Rat.add
    /// (CReal.seq x m) (Rat.natDivSucc 1 m)))` — the general
    /// self-approximation lemma every `CReal` satisfies: it never exceeds
    /// its own `m`-th sample by more than `1/(m+1)`. Via `x`'s own
    /// regularity read at `(n, m)` — the same shape
    /// [`Self::bucket_clamp_upper`] reads at `(n, j)` for the CLAMPED
    /// sample rather than `x` itself — widened from `1/(n+1)` up to the
    /// `2/(n+1)` `CReal.le`'s own definition asks for via
    /// `Rat.natDivSucc_le_add_left`. See `creal/uniform_continuity.rs`.
    pub sample_upper_bound: NameId,
    /// `CReal.sampleLowerBound : ∀ x m, CReal.le (CReal.ofRat (Rat.sub
    /// (CReal.seq x m) (Rat.natDivSucc 1 m))) x` — the other half of
    /// [`Self::sample_upper_bound`]: `x` is never below its own `m`-th
    /// sample by more than `1/(m+1)` either. Same route with the
    /// regularity indices swapped (`(m, n)` rather than `(n, m)`), mirroring
    /// how [`Self::bucket_clamp_lower`] swaps [`Self::bucket_clamp_upper`]'s
    /// own `(n, j)` to `(j, n)`. See `creal/uniform_continuity.rs`.
    pub sample_lower_bound: NameId,
    /// `CReal.bucketClose : ∀ (bnd : CReal) (m0 : Nat) (cap : Rat), Rat.le
    /// (Rat.sub (CReal.seq bnd j) (Rat.natDivSucc 1 j)) cap → ∀ (w : CReal),
    /// CReal.le CReal.zero w → CReal.le w bnd → CReal.le (CReal.abs
    /// (CReal.add w (CReal.neg (CReal.ofRat (Rat.min (Rat.natDivSucc
    /// (CReal.bucketIndex w k) k) cap))))) (CReal.ofRat (Rat.natDivSucc 1
    /// m0))` (`k := rescale_index(3, m0) = 4*m0+3`, `j := (Nat.succ k) *
    /// (Nat.succ k)`) — `w` is within `1/(m0+1)` of its own clamped
    /// grid-point sample. `k` is DERIVED from `m0`, not an independent
    /// parameter: the final widening step needs `k` to be exactly
    /// `rescale_index(3, m0)` (`Rat.natDivSucc_scale`'s own index), not
    /// merely large enough. Extracted from
    /// [`Self::bounded_of_uniformly_continuous`]'s covering argument, which
    /// used to assemble this fact inline. See
    /// `uniform_continuity::declare_bucket_close`.
    pub bucket_close: NameId,
    /// `CReal.abs_bound_of_self : ∀ x, le (abs x) (ofRat (natDivSucc
    /// (Nat.succ (CReal.bound x)) 0))` — `|x| ≤ mag_bound (bound x)`,
    /// unconditional for ANY `CReal`. Promoted from a private `fn` in
    /// `creal/uniform_continuity.rs` (it was inline scaffolding for
    /// [`Self::bounded_of_uniformly_continuous`]'s own covering argument
    /// and unreachable from any other file) to a `CRealPrelude` field, so
    /// `BoundedOn` is trivial to discharge for EVERY constant function on
    /// EVERY interval: `BoundedOn (fun _ => c) a b (CReal.bound c)`'s only
    /// content, after the range hypotheses are dropped, is this lemma
    /// applied at `c`. See `creal/uniform_continuity.rs`.
    pub abs_bound_of_self: NameId,
    /// `CReal.bounded_of_uniformly_continuous : ∀ F a b, UniformlyContinuousOn
    /// F a b → CReal.le a b → CReal.BoundedOn F a b K` for a COMPUTED `K`
    /// (never `Exists`-elimination — `K` is one Nat expression built from
    /// `F`, `a`, `b`, `huc` alone, so it is the SAME constant for every `z`).
    /// Spivak ch.7: a function uniformly continuous on `[a,b]` is bounded
    /// there. See `creal/uniform_continuity.rs`'s own
    /// `declare_bounded_of_uniformly_continuous` for the covering argument
    /// (now via [`Self::bucket_close`] rather than inline).
    pub bounded_of_uniformly_continuous: NameId,
    /// `CReal.ratSqLe : ∀ (u s : Rat), Rat.le (u*u) (s*s) → Rat.le Rat.zero s
    /// → Rat.le u s` — a purely rational fact (no `CReal` structure), proved
    /// via `Rat.mul_pos` and a difference-of-squares identity rather than a
    /// zero-divisor split. See `creal/mul_self_zero.rs`.
    pub rat_sq_le: NameId,
    /// `CReal.ratSqSandwich : ∀ (t s : Rat), Rat.le (t*t) (s*s) →
    /// Rat.le Rat.zero s → CReal.Within t s`. Applies [`Self::rat_sq_le`] to
    /// `t` and to `-t`.
    pub rat_sq_sandwich: NameId,
    /// `CReal.ratIndexRatioLeOne : ∀ (a : Nat), Rat.le (natDivSucc a a)
    /// Rat.one` — generalizes `Rat.nat_div_succ_le_one` to a numerator
    /// matched to its own index.
    pub rat_index_ratio_le_one: NameId,
    /// `CReal.ratUnitEqOne : Eq Rat (natDivSucc 1 0) Rat.one` — the cheap
    /// bridge between `natDivSucc`'s own "1" and the field's `Rat.one`,
    /// via `Rat.self_normalize` applied to `Rat.one` itself (no gcd/cross-
    /// multiplication reasoning needed: `num`/`den` are structure
    /// projections of `Rat.one`'s direct `mk`, and `normalize`'s proof
    /// argument is proof-irrelevant).
    pub rat_unit_eq_one: NameId,
    /// `CReal.eq_zero_of_mul_self_zero : ∀ x, Equiv (mul x x) zero → Equiv x
    /// zero`. See `creal/mul_self_zero.rs`.
    pub eq_zero_of_mul_self_zero: NameId,
    /// `CReal.eq_zero_of_add_eq_zero_of_nonneg : ∀ a b, le zero a → le zero b →
    /// Equiv (add a b) zero → Equiv a zero`.
    ///
    /// Nonnegative summands of a zero sum are each zero — an ordinary
    /// ordered-field fact this development was missing. Route: `a ≤ a + b`
    /// from `0 ≤ b` (`add_le_add` at `add a zero`/`add a b`, transported
    /// across `add_zero` by `le_congr`); `a + b ~ 0` gives `a + b ≤ 0`
    /// (`le_of_equiv`); `le_trans` gives `a ≤ 0`; with `0 ≤ a` and
    /// `equiv_of_le_le`, `a ~ 0`. See `creal/order_extra.rs`.
    pub eq_zero_of_add_eq_zero_of_nonneg: NameId,

    /// `CReal.le_of_forall_le_add_small : ∀ x y,
    /// (∀ e : Nat, le x (add y (ofRat (natDivSucc 1 e)))) → le x y`.
    ///
    /// **The Archimedean squeeze bridge**, from an abstract `∀e` accuracy
    /// family down to `CReal.le`'s own seq-level `∀n` shape. Fixing the goal
    /// index `n`, instantiating the hypothesis at the SAME accuracy/sample
    /// index `j` gives `x_j − y_{2j+1} ≤ 3/(j+1)` (`Rat.le_of_sub_le` /
    /// `Rat.sub_le_of_le` around the hypothesis's own `add`), and two
    /// `CReal.regular` round trips — `x_n ↔ x_j` and `y_{2j+1} ↔ y_n` — pay a
    /// further `1/(n+1)+1/(j+1)` and `1/(2j+2)+1/(n+1)`. `1/(2j+2) ≤ 1/(j+1)`
    /// (no antitone-in-index lemma: `1/(2j+2)+1/(2j+2) = 1/(j+1)` by
    /// `Rat.natDivSucc_add`+`Rat.natDivSucc_halve`, then `a ≤ a+a` from
    /// nonnegativity) folds the total to `2/(n+1) + 5/(j+1)`, and
    /// `Rat.le_of_le_add_natDivSucc` (`k = 5`) closes it. See
    /// `creal/archimedean_squeeze.rs`.
    pub le_of_forall_le_add_small: NameId,
    /// `CReal.equiv_zero_of_small : ∀ v,
    /// (∀ e : Nat, le (abs v) (ofRat (natDivSucc 1 e))) → Equiv v zero`.
    ///
    /// A thin wrapper over [`Self::le_of_forall_le_add_small`], applied
    /// twice: `le v zero` from `le_abs_self`/`le_trans` transported across
    /// `add_zero`/`add_comm`, and `le zero v` from `neg_le_abs`/`add_le_add`
    /// transported across `add_neg`. `equiv_of_le_le` closes both into one
    /// `Equiv`. See `creal/archimedean_squeeze.rs`.
    pub equiv_zero_of_small: NameId,
    /// `CReal.le_of_forall_le_add_rate : ∀ k x y,
    /// (∀ e : Nat, le x (add y (ofRat (natDivSucc k e)))) → le x y`.
    ///
    /// The rate-`K` generalization of [`Self::le_of_forall_le_add_small`]
    /// (which is now this lemma's `k := 1` instance, a thin wrapper). Only
    /// the hypothesis's own accuracy family scales with `k` — the two
    /// `CReal.regular` round trips are the representation's own rate-1
    /// Cauchy modulus and never see `k` — so term B fuses to `(k+2)/(j+1)`
    /// (was the literal `3/(j+1)`) and the final bound is
    /// `2/(n+1) + (k+4)/(j+1)`, closed by `Rat.le_of_le_add_natDivSucc` at
    /// the **symbolic** `k+4` (already general in its own `k` argument, so
    /// this needed no change). See `creal/archimedean_squeeze.rs`.
    pub le_of_forall_le_add_rate: NameId,
    /// `CReal.equiv_zero_of_rate : ∀ k v,
    /// (∀ e : Nat, le (abs v) (ofRat (natDivSucc k e))) → Equiv v zero`.
    ///
    /// The rate-`K` generalization of [`Self::equiv_zero_of_small`] (which is
    /// now this lemma's `k := 1` instance). Same two-sided-bound proof as the
    /// `k = 1` case, through [`Self::le_of_forall_le_add_rate`] at the same
    /// `k`. See `creal/archimedean_squeeze.rs`.
    pub equiv_zero_of_rate: NameId,

    // --- the integer square root (creal/sqrt.rs) ------------------------------
    /// `CReal.natSqrt : Nat -> Nat`, the missing computational primitive
    /// behind `CReal.sqrt`. See `creal/sqrt.rs`.
    pub nat_sqrt: NameId,
    /// `CReal.natSqrtSpec : ∀ n, And (Le (natSqrt n * natSqrt n) n)
    /// (Lt n (succ (natSqrt n) * succ (natSqrt n)))`.
    pub nat_sqrt_spec: NameId,
    /// `CReal.natSqrtLe : ∀ n, Le (natSqrt n * natSqrt n) n`.
    pub nat_sqrt_le: NameId,
    /// `CReal.natSqrtLt : ∀ n, Lt n (succ (natSqrt n) * succ (natSqrt n))`.
    pub nat_sqrt_lt: NameId,
    /// `CReal.sqrtApprox : CReal → Nat → Rat` — the rational square-root
    /// approximant `CReal.sqrt` is built from. See `creal/sqrt.rs` for the
    /// exact schedule; **no `Regular` proof exists for it yet** (that is the
    /// open obligation `CReal.sqrt` still needs). [`Self::sqrt_approx_sq_bracket`]
    /// is the same-index quality bound that obligation has to be built from;
    /// see its own doc for exactly what remains (a `KRegular` proof, not a
    /// `Regular` one directly — [`Self::regular_of_kregular`] already closes
    /// the constant-factor-to-exact gap generically).
    pub sqrt_approx: NameId,
    /// `CReal.sqrtApproxSqBracket : ∀ x n,
    /// And (Rat.le (Rat.mul (sqrtApprox x n) (sqrtApprox x n)) q)
    ///     (Rat.lt q (Rat.mul s1 s1))`, `q := Rat.max (CReal.seq x
    /// ((succ n)*(succ n))) Rat.zero`, `s1` the next `natSqrt` candidate up.
    /// The single-index approximation-quality bracket `sqrtApprox` was built
    /// to satisfy. See `creal/sqrt.rs`.
    pub sqrt_approx_sq_bracket: NameId,
    /// `CReal.sqrtApproxKRegular : ∀ x, KRegular (sqrtApprox x) 1` — the
    /// cross-index estimate `sqrt.rs`'s own module doc names as the
    /// remaining obligation: `sqrtApprox x` is regular up to the constant
    /// factor `2` (`c = 1`), independent of any magnitude bound on `x`. See
    /// `creal/sqrt.rs`.
    pub sqrt_approx_kregular: NameId,
    /// `CReal.sqrt : CReal → CReal := fun x => CReal.mk (speedup (sqrtApprox
    /// x) 1) (regular_of_kregular (sqrtApprox x) 1 (sqrtApproxKRegular x))`.
    ///
    /// Total (no `0 ≤ x` hypothesis in its signature): `sqrtApprox` clamps
    /// every sample to `Rat.max _ 0` before taking a `Nat` square root, so
    /// the construction never inspects `x`'s sign. `0 ≤ x` is the hypothesis
    /// `sqrt`'s own LAWS need (relating `sqrt x` back to `x`), not the
    /// definition. See `creal/sqrt.rs`.
    pub sqrt: NameId,
    /// `CReal.sqrt_congr : ∀ x y, Equiv x y → Equiv (sqrt x) (sqrt y)`.
    ///
    /// The cross-real analogue of `sqrtApproxKRegular`'s same-real,
    /// two-index estimate: same bracket, same `sum_sq_le_sq_sum`/`rat_sq_le`
    /// squeeze, but comparing two reals at one shared index via `Equiv`
    /// instead of one real at two indices via its own `regular`. Total, no
    /// `0 ≤ x`/`0 ≤ y` hypothesis — same reason `sqrt` itself needs none.
    /// See `creal/sqrt.rs`.
    pub sqrt_congr: NameId,
    /// `CReal.sqrt_one : Equiv (sqrt one) one`. `sqrtApprox one` is clamped
    /// to a CONSTANT sample (`seq one _` beta-reduces to `Rat.one`
    /// regardless of index), so `sqrt_approx_sq_bracket`'s two halves at
    /// `x := one` are already bounds against the fixed value `Rat.one` —
    /// `rat_sq_le` closes each side directly, no cross-index regularity or
    /// natSqrt-uniqueness argument needed. See `creal/sqrt.rs`.
    pub sqrt_one: NameId,
    /// `CReal.sqrt_zero : Equiv (sqrt zero) zero`. The same constant-sample
    /// shortcut as `sqrt_one`, simpler still: `sqrtApprox zero m` collapses
    /// to EXACTLY `Rat.zero` via `Rat.le_antisymm`, so `Within (u-0) bound`
    /// is trivial for any nonnegative bound. See `creal/sqrt.rs`.
    pub sqrt_zero: NameId,
    /// `CReal.sqrt_le_sqrt : ∀ x y, le x y → le (sqrt x) (sqrt y)`.
    ///
    /// **Total, no `0 ≤ x` hypothesis** — `le x y` alone suffices. This is
    /// the forward-only, `Rat.le`-only half of `sqrt_congr`'s argument:
    /// `sqrt_congr` needs a two-sided `Equiv` estimate (built from `Within`,
    /// hence needing both directions and `And.intro`); `le`'s one-sided
    /// `∀ n, seq x n − seq y n ≤ 2/(n+1)` instantiates directly at the shared
    /// deep index, with no `halves` extraction needed, and only the
    /// "forward" cross-real squeeze is run once (no `Equiv.symm`/backward
    /// direction, no negation to combine two halves). See `creal/sqrt.rs`.
    pub sqrt_le_sqrt: NameId,
    /// `CReal.sqrt_sq : ∀ x, le zero x → Equiv (sqrt (mul x x)) x`.
    ///
    /// The direction `complex.rs` actually needs (not `sq_sqrt`): cancelling
    /// the square in `‖z+w‖² ≤ (‖z‖+‖w‖)²` (the CAUCHY–SCHWARZ route,
    /// `Self::le_of_sq_le`'s consumer — a loose `2‖z‖²+2‖w‖²` bound was tried
    /// first and refuted, see `ComplexPrelude::norm_sq_add_le`'s own doc for
    /// the counterexample) is `sqrt_sq` at `t := abs z + abs w`. See
    /// `creal/sqrt.rs`'s own doc for the proof sketch — the genuinely new
    /// ingredient is recovering `t` (not `|t|`) from a two-sided bound on
    /// `t·t`, via [`crate::RatPrelude::lt_of_sq_lt`], the strict companion to
    /// `ratSqLe` this required.
    pub sqrt_sq: NameId,
    /// `CReal.sqrt_nonneg : ∀ x, CReal.le CReal.zero (sqrt x)`.
    ///
    /// Unconditional, unlike `sqrt_sq`/`mul_self_sqrt`: this never relates
    /// `sqrt x` back to `x` itself, only to `sqrtApprox`'s own
    /// clamp-then-`natSqrt` shape, which is nonneg regardless of `x`'s sign.
    /// See `creal/sqrt.rs`.
    pub sqrt_nonneg: NameId,
    /// `CReal.mul_self_sqrt : ∀ x, CReal.le CReal.zero x → Equiv (mul (sqrt
    /// x) (sqrt x)) x`.
    ///
    /// The direction `sqrt_sq` (`sqrt (mul x x) ~ x`) does NOT give: those
    /// are different statements, composed only via a third fact that this
    /// one is. Needed for `CReal.sqrt_mul` and hence `Complex.abs_mul`. The
    /// upper bound is a direct chain (`sqrt_bracket_pieces`'s lower half plus
    /// `Rat.max_le` against `x`'s own regularity and the `0 ≤ x` slack); the
    /// lower bound needs a uniform magnitude bound on `sqrtApprox(x, k)`
    /// (`CReal.bound_within` + `CReal.rat_sq_le`) and
    /// `mul_self_zero::diff_of_squares` at `(u1, u)` to expand the bracket's
    /// width term. See `creal/sqrt.rs`.
    pub mul_self_sqrt: NameId,
    /// `CReal.sqrt_mul : ∀ x y, CReal.le CReal.zero x → CReal.le CReal.zero y
    /// → Equiv (sqrt (mul x y)) (mul (sqrt x) (sqrt y))`.
    ///
    /// Composed from already-landed facts, not a new epsilon estimate:
    /// `mul_self_sqrt(x)`/`mul_self_sqrt(y)` plus a ring rearrangement give
    /// `(sqrt x·sqrt y)² ~ x·y`; `sqrt_sq` at `t := mul (sqrt x) (sqrt y)`
    /// (nonneg via `mul_nonneg`/`sqrt_nonneg`) gives `sqrt(t²) ~ t`; and
    /// `sqrt_congr` carries the first equivalence through `sqrt`, chaining
    /// to `sqrt (mul x y) ~ mul (sqrt x) (sqrt y)`. See `creal/sqrt.rs`.
    pub sqrt_mul: NameId,
    /// `CReal.le_of_sq_le : ∀ t s, le zero t → le zero s → le (mul t t) (mul
    /// s s) → le t s`.
    ///
    /// "Cancel the square" at the `CReal` level — the `CReal` analogue of
    /// [`crate::RatPrelude::lt_of_sq_lt`] (`Rat`, strict). `Complex.abs_add_le`
    /// (landed, `complex.rs`) uses this at `t := abs (Re (z · conj w))`,
    /// `s := abs z · abs w` — NOT at the final sqrt-cancellation step, which
    /// needs only `sqrt_le_sqrt`/`sqrt_sq` directly, both nonneg already —
    /// because `t` there is an `abs`, whose nonnegativity is unconditional,
    /// where the RAW Cauchy–Schwarz cross term is not (see
    /// `ComplexPrelude::abs_add_le`'s own doc, and
    /// [`Self::mul_self_abs`]). Composable from already-landed facts, no new
    /// epsilon estimate:
    /// `sqrt_le_sqrt` on the hypothesis gives `sqrt(t·t) ≤ sqrt(s·s)`;
    /// `sqrt_sq` at `t` and at `s` (using the two nonnegativity hypotheses)
    /// give `sqrt(t·t) ~ t` and `sqrt(s·s) ~ s`; `le_congr` transports the
    /// `le` fact across both at once. See `creal/sqrt.rs`.
    pub le_of_sq_le: NameId,

    // --- Bishop's speed-up combinator (creal/speedup.rs) ----------------------
    /// `CReal.KRegular : (Nat → Rat) → Nat → Prop` — Bishop regularity up to a
    /// constant factor: `KRegular f c := ∀ m n, Within (f m − f n)
    /// (natDivSucc (c+1) m + natDivSucc (c+1) n)`, i.e. `|f m − f n| ≤
    /// (c+1)/(m+1) + (c+1)/(n+1)`. Parametrized by `c` (so the constant
    /// factor is `c+1`) for the same reason [`Self::mul_shift`]/
    /// `product::mul_index` are: it keeps the sampling index `(c+1)·n + c`
    /// and its read-back (`Rat.natDivSucc_scale`) addition-only, with **no
    /// `Nat.sub`**.
    pub k_regular_pred: NameId,
    /// `CReal.speedup : (Nat → Rat) → Nat → Nat → Rat` —
    /// `speedup f c n := f ((c+1)·n + c)`, Bishop's speed-up combinator: it
    /// resamples `f` deep enough that a `KRegular f c` bound reads back as an
    /// exact `Regular` one. Same index shape as `product::mul_index` (reused
    /// directly), so every future construction that produces a `KRegular`
    /// sequence gets `CReal.mk` for free through
    /// [`Self::regular_of_kregular`].
    pub speedup: NameId,
    /// `CReal.regular_of_kregular : ∀ f c, KRegular f c → Regular (speedup f
    /// c)` — **the headline result**, and exact: `Rat.natDivSucc_scale` reads
    /// the `KRegular` bound at the speed-up indices back to `Regular`'s own
    /// modulus with no further estimate, unlike `product::regular_between`
    /// (which accepts any crude constant because it is comparing samples of
    /// an **already `Regular`** `CReal` at two different indices — a
    /// different problem from promoting a raw `KRegular` function, which is
    /// what this closes).
    pub regular_of_kregular: NameId,
    /// `CReal.speedup_close : ∀ f c, KRegular f c → ∀ n, Within (f n −
    /// speedup f c n) (natDivSucc (c+1) n + natDivSucc 1 n)`.
    ///
    /// **A bound, not an equivalence.** It measures how far the original
    /// sample `f n` sits from the speed-up's sample at the same index (both
    /// sides are plain rationals — `speedup`'s regularity is not consumed
    /// here, only `KRegular` itself), and the bound does shrink in `n` but is
    /// not the exact `Regular` modulus. It does **not** by itself give any
    /// `CReal.Equiv` between `f` and its speed-up: that needs `f` packaged as
    /// a `CReal` in the first place, which a bare `KRegular f c` hypothesis
    /// does not supply.
    pub speedup_close: NameId,

    // --- finite sums over ℝ (creal/series.rs) ---------------------------------
    /// `CReal.sumRange : (Nat → CReal) → Nat → CReal`, by structural `Nat.rec`
    /// on the bound — `sumRange f zero ≡ zero`, `sumRange f (succ j) ≡ add
    /// (sumRange f j) (f j)` — matching `Nat.sumRange`'s own convention
    /// (`nat_prelude/defs.rs::declare_finite_ranges`) and
    /// `Complex.sumRange`'s (`complex.rs::declare_sum_range`): recursion on
    /// the bound, the new term added on the **right** of the prior sum.
    /// `sumRange f n` is `Σ_{k<n} f k`.
    pub sum_range: NameId,
    /// `CReal.sumRange_zero : Eq CReal (sumRange f Nat.zero) zero`.
    ///
    /// Closes by `Eq.refl` alone, exactly as
    /// [`Complex.sumRange_zero`](crate::ComplexPrelude::sum_range_zero) does:
    /// `sumRange`'s `Nat.rec` application ι-reduces to the literal term
    /// `zero` at the base case, with no `CReal.add`/`CReal.mul` internals
    /// ever unfolded.
    pub sum_range_zero: NameId,
    /// `CReal.sumRange_succ : Eq CReal (sumRange f (Nat.succ n)) (add
    /// (sumRange f n) (f n))`. Closes by `Eq.refl` alone, for the same
    /// reason [`Self::sum_range_zero`] does.
    pub sum_range_succ: NameId,
    /// `CReal.sumRange_congr : ∀ f g n, (∀ i, Equiv (f i) (g i)) → Equiv
    /// (sumRange f n) (sumRange g n)`.
    ///
    /// **Load-bearing, and not skippable**: `CReal.Equiv` is a *defined*
    /// `Prop` relation, not `Eq`, so nothing rewrites under a `sumRange` for
    /// free and `funext` is not available (nor permitted). Induction on `n`,
    /// mirroring `Complex.sumRange_congr`'s own proof shape.
    pub sum_range_congr: NameId,
    /// `CReal.sumRange_add : ∀ f g n, Equiv (sumRange (fun i => add (f i) (g
    /// i)) n) (add (sumRange f n) (sumRange g n))`.
    ///
    /// Induction on `n`; the successor case needs the four-term
    /// rearrangement `(A+B)+(C+D) ~ (A+C)+(B+D)`, proved inline
    /// (`series::add4_comm`) the way `nat_prelude/binomial.rs::
    /// add_add_add_comm` does for `Eq Nat`, promoted to `Equiv` throughout.
    pub sum_range_add: NameId,
    /// `CReal.mul_sumRange : ∀ w f n, Equiv (mul w (sumRange f n))
    /// (sumRange (fun i => mul w (f i)) n)` — a constant distributes through
    /// a finite sum. Induction on `n`, mirroring `Complex.mul_sumRange`'s own
    /// proof shape (`left_distrib` at the step, `mul_zero` at the base).
    pub mul_sum_range: NameId,
    /// `CReal.sumRange_le : ∀ f g n, (∀ i, Nat.lt i n → le (f i) (g i)) → le
    /// (sumRange f n) (sumRange g n)` — monotonicity of a finite sum, with the
    /// pointwise hypothesis restricted to indices below the bound (mirroring
    /// `Nat.sumRange_congr_lt`'s hypothesis-threading shape,
    /// `nat_prelude/binomial.rs::declare_sum_range_congr_lt`, promoted from
    /// `Eq` to `CReal.le`). The first genuinely analytic fact in this file,
    /// and what every comparison argument over a finite sum needs.
    pub sum_range_le: NameId,
    /// `CReal.abs_sumRange_le : ∀ f n, le (abs (sumRange f n)) (sumRange
    /// (fun k => abs (f k)) n)` — the triangle inequality for finite sums,
    /// `|Σf| ≤ Σ|f|`. Induction on `n`, closing each step through an inline
    /// two-term triangle-inequality helper (`series::abs_add_le`) built from
    /// [`Self::abs_le`], [`Self::le_abs_self`] and [`Self::neg_le_abs`], which
    /// in turn needs `neg(add a b) ~ add (neg a) (neg b)` (`series::neg_add`,
    /// derived from `series::add4_comm` and the additive-inverse laws —
    /// `CReal` has no standalone `neg_add` law of its own, so this is proved
    /// inline rather than declared).
    pub abs_sum_range_le: NameId,
    /// `CReal.monotone_of_le_succ : ∀ f, (∀ n, le (f n) (f (Nat.succ n))) → ∀
    /// a b, Nat.le a b → le (f a) (f b)` — the `CReal`-valued analogue of
    /// `Nat.monotone_of_le_succ` (`nat_prelude/order.rs::declare_order`):
    /// adjacent-step monotonicity for an arbitrary `Nat → CReal` sequence
    /// implies full monotonicity across `Nat.le`. Proved by the identical
    /// scaffold — eliminating the `Nat.le a b` derivation via `Nat.le`'s own
    /// recursor (accessed through [`crate::nat_prelude::NatOps::prelude`]'s
    /// `le_rec`), a `Prop`-into-`Prop` elimination and so never restricted by
    /// `Exists.rec`'s data-elimination ban — with `CReal.le_refl`/
    /// `CReal.le_trans` standing in for `Nat`'s own. This is genuinely new:
    /// nothing in `creal/monotone.rs` compares a sequence across two
    /// **different** outer indices, only same-index Cauchy/regularity facts
    /// or derivative-driven monotonicity of a continuous `CReal → CReal`
    /// function — never a bare `Nat`-indexed sequence.
    pub mono_of_le_succ: NameId,
    /// `CReal.sumRange_mono_outer : ∀ f, (∀ i, le zero (f i)) → ∀ m n, Nat.le
    /// m n → le (sumRange f m) (sumRange f n)` — monotonicity of a finite sum
    /// in the **outer** index (`m`/`n`, the summation bound), for a
    /// pointwise-nonnegative summand. Distinct in kind from
    /// [`Self::sum_range_le`], which compares two *different summands* at the
    /// *same* bound. Built from [`Self::mono_of_le_succ`] applied to
    /// `sumRange f`, with the adjacent step `le (sumRange f n) (sumRange f
    /// (Nat.succ n))` proved from `sumRange_succ`'s defeq (`sumRange f (succ
    /// n) ≡ add (sumRange f n) (f n)`) plus the shift-by-a-nonneg-summand
    /// shape (`x ≤ x + w` from `w ≥ 0`, via `add_le_add`/`add_zero`/
    /// `le_congr` — the same three-line argument `creal/monotone.rs`'s
    /// private `shift_le_of_nonneg` makes, re-derived here rather than
    /// imported since that helper is not `pub(super)`). This is exactly the
    /// "monotonicity-in-the-outer-index" lemma `CReal.e`'s own construction
    /// named as its still-missing prerequisite for `2 ≤ e ≤ 3`.
    pub sum_range_mono_outer: NameId,
    /// `CReal.sumRange_telescope : ∀ f n, Equiv (sumRange (fun k => add (f
    /// (succ k)) (neg (f k))) n) (add (f n) (neg (f Nat.zero)))` —
    /// `Σ_{k<n} (f(k+1) − f k) ~ f n − f 0`. Induction on `n`; the base case
    /// is `symm add_neg`, the successor step is the four-term cancellation
    /// `series::cancel_left` (`(a+b)+(c+(−a)) ~ c+b`, built from
    /// `series::add4_comm` plus one more `add_neg`).
    pub sum_range_telescope: NameId,
    /// `CReal.sumRange_split : ∀ f m n, Equiv (sumRange f (add m n)) (add
    /// (sumRange f m) (sumRange (fun k => f (add m k)) n))` — splitting a sum
    /// at `m` turns a statement about the tail into a statement about a
    /// difference of partial sums. Induction on `n`; both cases close by
    /// `Nat.add`'s own iota-reduction (`add m Nat.zero ≡ m`, `add m (succ j)
    /// ≡ succ (add m j)`) plus one `add_zero`/`add_assoc` respectively — no
    /// new rational estimate.
    pub sum_range_split: NameId,
    /// `CReal.sumRange_telescope_ge : ∀ f bound k,
    /// (∀ i, Nat.lt i k → le bound (add (f (Nat.succ i)) (neg (f i)))) →
    /// le (sumRange (fun _ => bound) k) (add (f k) (neg (f Nat.zero)))`
    /// (`creal/monotone.rs`) — the symbolic-length subdivision lemma: `k`
    /// pieces each bounded below telescope to a lower bound on the total
    /// difference, `k` itself left symbolic (composed from
    /// [`Self::sum_range_le`] and [`Self::sum_range_telescope`] via
    /// [`Self::le_congr`], not a new estimate). The first consumer is
    /// [`Self::monotone_of_nonneg_deriv`].
    pub sum_range_telescope_ge: NameId,
    /// `CReal.sumRange_telescope_le : ∀ f bound k,
    /// (∀ i, Nat.lt i k → le (add (f (Nat.succ i)) (neg (f i))) bound) →
    /// le (add (f k) (neg (f Nat.zero))) (sumRange (fun _ => bound) k)`
    /// (`creal/monotone.rs`) — the mirror of [`Self::sum_range_telescope_ge`]:
    /// `k` pieces each bounded above telescope to an upper bound on the
    /// total difference.
    pub sum_range_telescope_le: NameId,
    /// `CReal.sumRange_tail_le : ∀ f g m n, (∀ k, le (abs (f k)) (g k)) → le
    /// (abs (add (sumRange f (add m n)) (neg (sumRange f m)))) (add
    /// (sumRange g (add m n)) (neg (sumRange g m)))` — **the comparison
    /// test**: if `f` is pointwise bounded by `g` in absolute value, the
    /// `m`-to-`m+n` tail of `f`'s partial sums is bounded by the
    /// corresponding tail of `g`'s. Not stated through `CReal.Cauchy`
    /// (`creal/convergence.rs`) — see `series.rs`'s module documentation for
    /// why: `Cauchy`'s body compares `seq (h m) m` against `seq (h n) n`, the
    /// RATIONAL sample each real offers at *its own canonical index*.
    /// [`Self::sum_range_seq_succ`] now supplies the recursive form of that
    /// sample-rate law; reaching the literal `CReal.Cauchy` predicate from
    /// this theorem plus that one is still a separate, unbuilt bridge (see
    /// the module documentation for exactly what is missing and why the
    /// recursive law alone is not enough). This theorem remains the actual
    /// mathematical engine of the comparison test (a real-valued tail bound,
    /// via `sum_range_split` + `abs_sumRange_le` + `sumRange_le`).
    pub sum_range_tail_le: NameId,
    /// `CReal.sumRange_tail_within : ∀ f g m n, (∀ k, le (abs (f k)) (g k)) →
    /// Within (seq (add (sumRange f (add m n)) (neg (sumRange f m))) (add m
    /// n)) (add (seq (add (sumRange g (add m n)) (neg (sumRange g m))) (add m
    /// n)) (natDivSucc 2 (add m n)))` — [`Self::sum_range_tail_le`]'s
    /// `CReal.le`, unfolded at its own tail's defining index `add m n` and
    /// repackaged as a `Within` bound on that same RATIONAL sample, widened
    /// by `2/(add m n + 1)`. Built from **two** one-sided applications
    /// ([`Self::le_abs_self`]/[`Self::neg_le_abs`] chained through
    /// [`Self::le_trans`] against `sum_range_tail_le`'s conclusion, then each
    /// applied at `add m n`) via `series::within_of_tail_le` (the
    /// "within-swap via `neg_sub`"-shaped helper `series.rs`'s module
    /// documentation names as the first piece to land), **not** one `abs_le`
    /// call — `abs_le`'s hypothesis shape does not survive sampling at an
    /// index. This is the `f`-side leg [`Self::sum_range_tail_within_cauchy`]
    /// (the outer telescope) combines with a bound on this theorem's own
    /// `g`-side sample; that `g`-side bound, through a Cauchy witness for
    /// `sumRange g`, is [`Self::sum_range_tail_cauchy_within`] (the inner
    /// telescope).
    pub sum_range_tail_within: NameId,
    /// `CReal.sumRange_tail_within_le : ∀ f g, (∀ k, le (abs (f k)) (g k)) →
    /// ∀ a b, Nat.le a b → Within (seq (add (sumRange f b) (neg (sumRange f
    /// a))) b) (add (seq (add (sumRange g b) (neg (sumRange g a))) b)
    /// (natDivSucc 2 b))` — the **Nat.le_total case split**'s content, first
    /// half: lifts [`Self::sum_range_tail_within`]'s ordered-pair form `(m,
    /// add m n)` to an arbitrary pair `(a, b)` constrained only by `a ≤ b`,
    /// which `series.rs`'s module documentation names as needed to reach
    /// `CReal.Cauchy`'s arbitrary-pair `∀ m n` shape.
    ///
    /// Built from `Nat.le_dest` (`a ≤ b → ∃ k, add a k = b`), one application
    /// of [`Self::sum_range_tail_within`] at `(a, k)`, and one `Nat`-equality
    /// rewrite (`series::nat_rewrite_prop`-style transport) carrying the
    /// witnessed instance's index `add a k` over to `b`. The mirror direction
    /// (`b ≤ a`) needs no new machinery — it is this same theorem applied
    /// with `a`/`b` swapped — so this theorem supplies both halves' content;
    /// selecting between them via `Nat.le_total` is left to whichever future
    /// piece (the outer telescope) actually consumes the selection.
    pub sum_range_tail_within_le: NameId,
    /// `CReal.sumRange_tail_cauchy_within : ∀ g K, (∀ pp qq, Within (seq
    /// (sumRange g pp) pp − seq (sumRange g qq) qq) (natDivSucc K pp +
    /// natDivSucc K qq)) → ∀ m n, Within (seq (add (sumRange g (add m n))
    /// (neg (sumRange g m))) (add m n)) ((modulus t q + (natDivSucc K q +
    /// natDivSucc K m)) + modulus m t)`, `q := add m n`, `t := shift q` — the
    /// **inner telescope** `series.rs`'s module documentation and
    /// [`Self::sum_range_tail_within`]'s own doc comment name as unbuilt:
    /// bounds `sumRange_tail_within`'s `g`-side rational sample through a
    /// Cauchy witness for `sumRange g`, taken in its raw witnessed form (an
    /// explicit `K` plus the `∀ pp qq` bound) rather than as the
    /// existentially-quantified `CReal.Cauchy (sumRange g)`, so this theorem
    /// needs no `Exists.rec` motive of its own.
    ///
    /// A three-leg telescope at the shared index `t`, chained via **two**
    /// `Rat.sub_add_sub` rewrites and no `Rat.neg` anywhere (the three legs
    /// already share consecutive endpoints in the right order): `CReal.regular`
    /// at `(sumRange g q, t, q)`, the witnessed hypothesis applied at `(q,
    /// m)`, and `CReal.regular` at `(sumRange g m, m, t)`. The outer
    /// telescope — combining this with [`Self::sum_range_tail_within`]'s own
    /// bound — is [`Self::sum_range_tail_within_cauchy`].
    pub sum_range_tail_cauchy_within: NameId,
    /// `CReal.sumRange_tail_within_cauchy : ∀ f g, (∀ k, le (abs (f k)) (g
    /// k)) → ∀ K, (∀ pp qq, Within (seq (sumRange g pp) pp − seq (sumRange g
    /// qq) qq) (natDivSucc K pp + natDivSucc K qq)) → ∀ m n, Within (seq
    /// (add (sumRange f (add m n)) (neg (sumRange f m))) (add m n)) (add
    /// ((modulus t q + (natDivSucc K q + natDivSucc K m)) + modulus m t)
    /// (natDivSucc 2 (add m n)))`, `q := add m n`, `t := shift q` — the
    /// **outer telescope** `series.rs`'s module documentation names as the
    /// one piece left to combine [`Self::sum_range_tail_within`]'s bound
    /// (`Within u (v+w)`, the `f`-side real-valued tail bound unfolded at
    /// its own index) with [`Self::sum_range_tail_cauchy_within`]'s bound on
    /// that same `v` (`Within v B`, `v` built identically by both theorems
    /// from the same `m`, `n`, so no transport is needed to identify them).
    ///
    /// Built from nothing beyond `series::weaken` (`Within r q` + `q ≤ q'` →
    /// `Within r q'`) applied to `q := v+w`, `q' := B+w`: `q ≤ q'` is one
    /// `Rat.add_le_add` on the upper half of `sum_range_tail_cauchy_within`'s
    /// own conclusion (`le v B`, via `halves`) paired with `Rat.le_refl w`.
    /// The three-leg inner telescope and the two one-sided real bounds this
    /// composes already did the heavy lifting inside the two theorems named
    /// above; this one is bound-widening glue only, not a further telescope.
    pub sum_range_tail_within_cauchy: NameId,
    /// `CReal.sumRange_cauchy_dominated_ordered : ∀ f g k, (∀ x, le (abs (f
    /// x)) (g x)) → (∀ pp qq, Within (seq (sumRange g pp) pp − seq (sumRange
    /// g qq) qq) (natDivSucc k pp + natDivSucc k qq)) → ∀ a b, Nat.le a b →
    /// Within (seq (sumRange f b) b − seq (sumRange f a) a) (bound k a b)` —
    /// the ordered-pair half of wiring [`Self::sum_range_tail_within_cauchy`]
    /// through to [`Self::cauchy`]'s own **canonical** two-index sample
    /// shape (`seq (f p) p − seq (f q) q`, not the shifted-sample shape that
    /// theorem supplies). `series.rs`'s module documentation names this gap
    /// under "Cauchy-shape conversion": `sum_range_tail_within_cauchy`
    /// bounds `f`'s tail sampled at a *shared, shifted* index; reaching
    /// `Cauchy`'s own shape needs two more `CReal.regular` legs bridging
    /// each side back to its own canonical sample
    /// (`series::dominated_canonical_at`), and lifting the ordered pair
    /// `(m, add m gap)` that construction works with to an arbitrary
    /// `a ≤ b` (`Nat.le_dest` plus transport, the same technique
    /// [`Self::sum_range_tail_within_le`] already used to lift
    /// `sum_range_tail_within`, reused here against a different payload).
    ///
    /// Selecting between this pair's two orientations via `Nat.le_total`,
    /// and normalizing the resulting bound into `Cauchy`'s own
    /// `natDivSucc K m + natDivSucc K n` shape, are left to whichever piece
    /// assembles `sumRange_cauchy_of_dominated` itself.
    pub sum_range_cauchy_dominated_ordered: NameId,
    /// `CReal.sumRange_cauchy_dominated_ordered_normalized : ∀ f g k, (∀ x,
    /// le (abs (f x)) (g x)) → (∀ pp qq, Within (seq (sumRange g pp) pp − seq
    /// (sumRange g qq) qq) (natDivSucc k pp + natDivSucc k qq)) → ∀ a b,
    /// Nat.le a b → Within (seq (sumRange f b) b − seq (sumRange f a) a)
    /// (natDivSucc K' b + natDivSucc K' a)`, for an explicit `K'` built from
    /// `k` alone (`Nat.add`-with-literal chain, no fresh existential) —
    /// **bound normalization**, `series.rs`'s module documentation's second
    /// named gap. Post-processes [`Self::sum_range_cauchy_dominated_ordered`]'s
    /// own eleven-`natDivSucc`-leaf bound (four copies of `1/(shift b+1)`,
    /// widened to `1/(b+1)` via `half_shift_le`; the rest fused pairwise via
    /// `Rat.natDivSucc_add`) into the **single**, `Cauchy`-shaped two-term sum
    /// this development's `b`-side already reaches without padding (`K' :=
    /// k+8`) and its `a`-side reaches by one `Rat.natDivSucc_le_add_left` pad
    /// (`k+2 ↦ k+8`, defeq to `K'` since both are nested `Nat.add`-by-literal
    /// chains over the same `k`, needing no `Nat.add_assoc`/`Nat.add_comm`
    /// lemma to align — see `series.rs`'s doc for why this is pure
    /// computation). Still returns the **ordered-pair** shape (`a ≤ b`
    /// required, not yet `∀ a b` unconditionally) and takes the Cauchy
    /// hypothesis in its raw witnessed form (`k` a plain parameter, not
    /// wrapped in `∃`) — the `Nat.le_total` case split and the `CReal.Cauchy`
    /// existential itself are what [`Self::sum_range_cauchy_of_dominated`]
    /// adds on top of this theorem.
    pub sum_range_cauchy_dominated_ordered_normalized: NameId,
    /// `CReal.sumRange_cauchy_of_dominated : ∀ f g, (∀ k, le (abs (f k)) (g
    /// k)) → Cauchy (sumRange g) → Cauchy (sumRange f)` — the comparison
    /// test's Cauchy half, and `series.rs`'s module documentation's own
    /// goal: eliminate [`Self::cauchy`]'s existential on the hypothesis
    /// (`Exists.rec`, elem type `Nat`, `declare_converges_cauchy`'s own
    /// idiom, `creal/convergence.rs`), split `∀ m n` via the **decidable** `Nat.le_total` (never
    /// branch this way on the *undecidable* [`Self::le`] over `CReal`
    /// itself), and in each branch instantiate
    /// [`Self::sum_range_cauchy_dominated_ordered_normalized`] at whichever
    /// of `(m, n)`/`(n, m)` satisfies its `a ≤ b` side condition — one
    /// orientation lands exactly on `Cauchy`'s own `(m, n)` argument and
    /// sample order with no further work, the other needs one
    /// `within_symm` flip (the raw conclusion's difference is `seq (f n) n
    /// − seq (f m) m)`, `Cauchy` wants `seq (f m) m − seq (f n) n`) plus one
    /// `Rat.add_comm` (the two branches' `K'`-bounds arrive in opposite
    /// `radd` order relative to `Cauchy`'s fixed `(m, n)`). Wraps the result
    /// in `Exists.intro` at the same `K' := k+8` numerator
    /// `sum_range_cauchy_dominated_ordered_normalized` already produces.
    pub sum_range_cauchy_of_dominated: NameId,
    /// `CReal.sumRange_converges_of_dominated : ∀ f g, (∀ k, le (abs (f k))
    /// (g k)) → Cauchy (sumRange g) → Exists (fun L => Converges (sumRange f)
    /// L)` — the composition `series.rs`'s module documentation named as the
    /// remaining step once [`Self::converges_of_cauchy`] landed
    /// (`creal/convergence.rs`, the `Cauchy → Converges` bridge through
    /// `speedup`/`KRegular`, filling the gap that same documentation had
    /// earlier flagged as missing infrastructure). Introduces no existential
    /// of its own: applies [`Self::sum_range_cauchy_of_dominated`] to get
    /// `Cauchy (sumRange f)`, then [`Self::converges_of_cauchy`] directly —
    /// both already-declared theorems, composed by application alone.
    pub sum_range_converges_of_dominated: NameId,
    /// `CReal.sumRange_comparisonTest : ∀ a b, (∀ k, le zero (a k)) → (∀ k,
    /// le (a k) (b k)) → Exists (fun M => Converges (sumRange b) M) →
    /// Exists (fun L => Converges (sumRange a) L)` — the comparison test as
    /// usually stated (pointwise `0 ≤ a k ≤ b k`, `Σ b` convergent), rather
    /// than [`Self::sum_range_converges_of_dominated`]'s `Cauchy`-hypothesis
    /// form.
    ///
    /// Two conversions bridge the two forms: [`Self::converges_cauchy`]
    /// turns the `Exists … Converges (sumRange b) M` hypothesis into
    /// `Cauchy (sumRange b)` (eliminating the witness `M` into a target that
    /// does not mention it, `creal/convergence.rs`'s `exists_elim` reused
    /// over `CReal` rather than `Nat`); and `0 ≤ a k`/`a k ≤ b k` combine into
    /// `abs (a k) ≤ b k` via [`Self::abs_le`], whose second premise
    /// `neg (a k) ≤ b k` comes from `neg (a k) ≤ zero` (`Self::neg_le_neg` at
    /// `0 ≤ a k`, then the `Equiv (neg zero) zero` rewrite
    /// `series.rs::neg_zero_equiv` already builds for `power.rs`'s identical
    /// pattern) chained through `zero ≤ b k` (`Self::le_trans` of the two
    /// pointwise hypotheses) by one more [`Self::le_trans`]. Then
    /// [`Self::sum_range_converges_of_dominated`] closes it directly.
    pub sum_range_comparison_test: NameId,
    /// `CReal.sumRange_cauchy_of_abs_cauchy : ∀ f, Cauchy (sumRange (fun k =>
    /// abs (f k))) → Cauchy (sumRange f)` — absolute convergence implies
    /// convergence, `Cauchy` form. A direct corollary of
    /// [`Self::sum_range_cauchy_of_dominated`] at `g := fun k => abs (f k)`:
    /// the pointwise hypothesis `∀k, le (abs (f k)) (g k)` is `le_refl (abs
    /// (f k))` after one beta reduction on `g k`, so no new real-analysis
    /// content is needed. See `creal/series.rs::declare_sum_range_cauchy_of_abs_cauchy`.
    pub sum_range_cauchy_of_abs_cauchy: NameId,
    /// `CReal.sumRange_converges_of_abs_converges : ∀ f, Exists (fun M =>
    /// Converges (sumRange (fun k => abs (f k))) M) → Exists (fun L =>
    /// Converges (sumRange f) L)` — absolute convergence implies convergence,
    /// `Converges` form. Composes with [`Self::sum_range_comparison_test`]'s
    /// own output (applied at `fun k => abs (a k)`) to give the comparison
    /// test on a SIGNED series `a`, which `sum_range_comparison_test` cannot
    /// take directly since its first hypothesis is `∀k, 0 ≤ a k`. Eliminates
    /// the existential witness via [`Self::converges_cauchy`] into
    /// `Cauchy (sumRange (fun k => abs (f k)))`, then
    /// [`Self::sum_range_cauchy_of_abs_cauchy`] and
    /// [`Self::converges_of_cauchy`] close it directly. See
    /// `creal/series.rs::declare_sum_range_converges_of_abs_converges`.
    pub sum_range_converges_of_abs_converges: NameId,
    /// `CReal.sumRange_seq_zero : Eq Rat (seq (sumRange f Nat.zero) k)
    /// Rat.zero` — the base case of the sample-rate law, closing by `Eq.refl`
    /// alone (`sumRange f zero` ι-reduces to `zero := ofRat Rat.zero`, and
    /// `seq (ofRat q) k` ι-reduces to `q`).
    pub sum_range_seq_zero: NameId,
    /// `CReal.sumRange_seq_succ : ∀ f n k, Eq Rat (seq (sumRange f (Nat.succ
    /// n)) k) (add (seq (sumRange f n) (shift k)) (seq (f n) (shift k)))` —
    /// **the sample-rate law this file's own module documentation named as
    /// missing**, in its cheap recursive form: `sumRange f (succ n)`
    /// ι-reduces to `add (sumRange f n) (f n)`, and `seq (add x y) k`
    /// ι-reduces (through `CReal.add`'s own `mk (fun n => …) _`
    /// representative) to `seq x (shift k) + seq y (shift k)` — so the whole
    /// chain is ι+β, no case split and no rational estimate, exactly like
    /// [`Self::sum_range_zero`]/[`Self::sum_range_succ`]. Closing the general
    /// **closed form** this recursion implies (`seq (sumRange f n) k = Σ_{i<n}
    /// seq (f i) (shift^{n-i} k)`, `shift` iterated `n − i` times) as its own
    /// kernel theorem, and bridging from there (or from
    /// [`Self::sum_range_tail_le`] directly) to `CReal.Cauchy`/`Converges`,
    /// is unbuilt — see `series.rs`'s module documentation for why the
    /// closed form alone is not sufficient (each term's own regularity
    /// contributes an `Ω(1/i)` error that does not shrink with `n`, so a
    /// naive per-term bound diverges) and what the tractable next step looks
    /// like.
    pub sum_range_seq_succ: NameId,

    // --- powers, and the geometric series over ℝ (creal/power.rs) -----------
    /// `CReal.pow : CReal → Nat → CReal`, by structural `Nat.rec` on the
    /// exponent — `pow x Nat.zero ≡ one`, `pow x (Nat.succ j) ≡ mul (pow x
    /// j) x` — matching `Int.pow`/`Complex.pow`'s own convention verbatim
    /// (`int_prelude/defs.rs::declare_pow`, `complex.rs::declare_pow`):
    /// recursion on the exponent, the recursive factor `mul (pow x j) x`
    /// with the fresh copy on the **right** and the inductive value on the
    /// **left**.
    pub pow: NameId,
    /// `CReal.pow_zero : Eq CReal (pow x Nat.zero) one`. Closes by `Eq.refl`
    /// alone: `pow`'s `Nat.rec` application ι-reduces to the literal term
    /// `one` at the base case, with no `CReal.mul` internals ever unfolded.
    pub pow_zero: NameId,
    /// `CReal.pow_succ : ∀ x (m : Nat), Eq CReal (pow x (Nat.succ m)) (mul
    /// (pow x m) x)`. Closes by `Eq.refl` alone, for the same reason
    /// [`Self::pow_zero`] does.
    pub pow_succ: NameId,
    /// `CReal.pow_add : ∀ x (m n : Nat), Equiv (pow x (Nat.add m n)) (mul
    /// (pow x m) (pow x n))`. Induction on `n`, mirroring `Complex.pow_add`'s
    /// own proof shape (`complex.rs::declare_pow_add`) verbatim.
    pub pow_add: NameId,
    /// `CReal.pow_congr : ∀ x y, Equiv x y → ∀ n, Equiv (pow x n) (pow y
    /// n)`.
    ///
    /// **Load-bearing, and not skippable**: `CReal.Equiv` is a *defined*
    /// `Prop` relation, so nothing rewrites under `pow` for free and
    /// `funext` is unavailable. Induction on `n`, closing the step with
    /// [`Self::mul_congr`] against the outer `Equiv x y` hypothesis and the
    /// inductive hypothesis.
    pub pow_congr: NameId,
    /// `CReal.pow_nonneg : ∀ x, le zero x → ∀ n, le zero (pow x n)`.
    /// Induction on `n`: the base case is `le_of_lt zero_lt_one` up to
    /// `pow`'s ι-reduction, the step is [`Self::mul_nonneg`] against the
    /// inductive hypothesis and the outer hypothesis.
    pub pow_nonneg: NameId,
    /// `CReal.pow_le_one : ∀ x, le zero x → le x one → ∀ n, le (pow x n)
    /// one`. Induction on `n`: the base case is `le_refl one`, the step
    /// multiplies the inductive hypothesis `pow x j ≤ one` by the
    /// nonnegative `x` on the **left** ([`Self::mul_le_mul_of_nonneg_left`],
    /// giving `x·(pow x j) ≤ x·one ~ x`), chains through `x ≤ one`
    /// ([`Self::le_trans`]), and commutes the product back into `pow`'s own
    /// right-recursive shape (`mul_comm`+`le_congr`).
    pub pow_le_one: NameId,
    /// `CReal.mul_sub_one_geom : ∀ x (n : Nat), Equiv (mul (add one (neg x))
    /// (sumRange (fun k => pow x k) n)) (add one (neg (pow x n)))` — **the
    /// geometric series identity**, `(1 − x) · Σ_{k<n} xᵏ = 1 − xⁿ`, mirroring
    /// `Complex.mul_sub_one_geom` (`complex.rs::declare_mul_sub_one_geom`).
    ///
    /// Stated multiplied through, deliberately: the quotient form `Σ xᵏ ~
    /// (1−xⁿ)/(1−x)` needs `inv (1 − x)` with a *witnessed* `PosBound`, which
    /// no theorem can supply for an arbitrary `x`, and reaching it from `x ≁
    /// 1` would need Markov's principle, which this kernel neither proves nor
    /// assumes. The multiplied form holds for every `x`, including `x ~ 1`,
    /// where the quotient form is meaningless.
    pub mul_sub_one_geom: NameId,
    /// `CReal.geom_sum_bounded : ∀ x, le zero x → ∀ n, le (mul (add one (neg
    /// x)) (sumRange (fun k => pow x k) n)) one` — from [`Self::mul_sub_one_geom`]
    /// plus [`Self::pow_nonneg`].
    ///
    /// **Not** a bound on the partial sum `Σ xᵏ` itself (that needs `inv` and
    /// a witnessed modulus, exactly as the quotient form of
    /// [`Self::mul_sub_one_geom`] would), and **not** conditioned on `x ≤
    /// one`: only `0 ≤ x` is needed (to get `0 ≤ xⁿ`, hence `1 − xⁿ ≤ 1`) —
    /// for `x > 1` the multiplier `1 − x` is negative and the product is
    /// bounded by `1` even more trivially.
    pub geom_sum_bounded: NameId,
    /// `CReal.pow_le_pow_of_le_one : ∀ x, le zero x → le x one → ∀ n, le (pow
    /// x (Nat.succ n)) (pow x n)` — the powers are non-increasing on `[0,1]`.
    ///
    /// Not an induction: `pow`'s own ι-reduction identifies `pow x (succ n)`
    /// with `mul (pow x n) x` definitionally, so
    /// [`Self::mul_le_mul_of_nonneg_left`] at `a := pow x n` (nonnegative via
    /// [`Self::pow_nonneg`]) against the outer `x ≤ one` gives `mul (pow x n)
    /// x ≤ mul (pow x n) one`, and [`Self::mul_one`] folds the right side
    /// back to `pow x n` — one step, for an arbitrary fixed `n`.
    pub pow_le_pow_of_le_one: NameId,
    /// `CReal.mul_sub_one_geom_tail : ∀ x m n, Equiv (mul (add one (neg x))
    /// (add (sumRange (fun k => pow x k) (Nat.add m n)) (neg (sumRange (fun k
    /// => pow x k) m)))) (add (pow x m) (neg (pow x (Nat.add m n))))` — the
    /// geometric series identity applied to a **tail**: `(1−x)·(Σ_{k<m+n} xᵏ
    /// − Σ_{k<m} xᵏ) = xᵐ − xᵐ⁺ⁿ`.
    ///
    /// By induction on `n` with `m` fixed, reusing
    /// [`Self::mul_sub_one_geom`]'s own successor-step algebra verbatim (the
    /// accumulator generalised from the constant `one` to the variable `pow x
    /// m`), then converted from the shifted-partial-sum shape that induction
    /// produces into the direct tail above via [`Self::sum_range_split`] and
    /// one group cancellation — the same conversion
    /// [`Self::sum_range_tail_le`]'s own proof performs. Holds for **every**
    /// `x`, no hypothesis at all: this is the "multiplied through" form, for
    /// the same reason [`Self::mul_sub_one_geom`] is stated that way rather
    /// than as a quotient.
    pub mul_sub_one_geom_tail: NameId,
    /// `CReal.geom_tail_bounded : ∀ x, le zero x → ∀ m n, le (mul (add one
    /// (neg x)) (add (sumRange (fun k => pow x k) (Nat.add m n)) (neg
    /// (sumRange (fun k => pow x k) m)))) (pow x m)` — the real-valued tail
    /// bound: the multiplied-through tail is at most `xᵐ`, from
    /// [`Self::mul_sub_one_geom_tail`] plus [`Self::pow_nonneg`] (to drop the
    /// nonnegative `−xᵐ⁺ⁿ` term), mirroring [`Self::geom_sum_bounded`]'s own
    /// proof shape and its own decision to need only `0 ≤ x`.
    ///
    /// **Not** a bound on the tail `Σ_{k<m+n} xᵏ − Σ_{k<m} xᵏ` alone — that
    /// needs `inv (1−x)` with a witnessed `PosBound`, a nonnegativity lemma
    /// for `sumRange` of a pointwise-nonnegative function, and a rational
    /// inverse identity for `Rat.natDivSucc`, none of which this development
    /// builds; see the module documentation for the precise blocker.
    pub geom_tail_bounded: NameId,
    /// `CReal.geom_tail_bounded_div : ∀ x, le zero x → ∀ k (h : PosBound (add
    /// one (neg x)) k) m n, le (add (sumRange (fun j => pow x j) (Nat.add m
    /// n)) (neg (sumRange (fun j => pow x j) m))) (mul (inv (add one (neg x))
    /// k h) (pow x m))` — the **quotient form** of [`Self::geom_tail_bounded`]:
    /// `tail ≤ xᵐ / (1 − x)`, for `1 − x` bounded away from zero by a
    /// witnessed [`Self::pos_bound`] (see `geometric.rs`'s module
    /// documentation for why this is data, not a hypothesis on `x` itself).
    /// Multiplies [`Self::geom_tail_bounded`]'s conclusion through by `inv
    /// (add one (neg x)) k h` (nonnegative, [`Self::inv_nonneg`]) via
    /// [`Self::mul_le_mul_of_nonneg_left`], then cancels the resulting
    /// `mul inv (mul (1−x) tail)` down to `tail` using
    /// [`Self::mul_inv_cancel`] — the same `mul inv (mul c w) ≈ w` identity
    /// `creal/cancellation.rs::declare_le_of_mul_le_mul_left` builds, reused
    /// here in its more direct `mul_le_mul_of_nonneg_left`-then-cancel order
    /// rather than through that theorem's own `le (mul c x) (mul c y) → le x
    /// y` wrapper, because this bound's right-hand side (`pow x m`) is not
    /// already in `mul (1−x) _` shape.
    pub geom_tail_bounded_div: NameId,
    /// `CReal.geom_tail_within : ∀ x, le zero x → ∀ k (h : PosBound (add one
    /// (neg x)) k) m n, Within (seq (add (sumRange (fun j => pow x j) (Nat.add
    /// m n)) (neg (sumRange (fun j => pow x j) m))) (Nat.add m n)) (add (seq
    /// (mul (inv (add one (neg x)) k h) (pow x m)) (Nat.add m n)) (natDivSucc
    /// 2 (Nat.add m n)))` — [`Self::geom_tail_bounded_div`]'s real-valued
    /// bound, sampled at the tail's own canonical index `add m n` and
    /// repackaged as a `Within` bound, the way
    /// [`Self::sum_range_tail_within`] repackages
    /// [`Self::sum_range_tail_le`] — except the "other side" here is not a
    /// second sequence `g`'s tail but the single real quotient `xᵐ/(1−x)`,
    /// whose own rational sample at `add m n` is carried forward rather than
    /// closed into a `natDivSucc`-shaped constant (that closure needs a
    /// geometric-decay-dominates-harmonic-rate estimate this development does
    /// not yet build; see `geometric.rs`'s module documentation).
    ///
    /// Built from three pieces: [`Self::geom_tail_bounded_div`] itself
    /// (`le tail Y`), a fresh nonnegativity proof for the tail
    /// (`geometric.rs`'s own `geom_tail_nonneg`, via [`Self::sum_range_split`]
    /// with [`Self::pow_nonneg`] — **not** available as a named theorem
    /// elsewhere, since `series.rs`'s own module documentation lists a
    /// nonnegativity lemma for `sumRange` of a pointwise-nonnegative function
    /// among what it does not build), and `Y`'s own nonnegativity
    /// ([`Self::inv_nonneg`] times [`Self::pow_nonneg`] via
    /// [`Self::mul_nonneg`]) to get `le (neg tail) Y`. Applying both `CReal.le`
    /// facts directly to the shared index `add m n` (each unfolds to its own
    /// `Rat.le` bound at that index, exactly as
    /// [`Self::sum_range_tail_within`]'s own proof applies `sum_range_tail_le`
    /// to an index) and combining via the "within-swap via `neg_sub`" pattern
    /// closes the `Within`.
    pub geom_tail_within: NameId,
    /// `CReal.geom_tail_within_le : ∀ x, le zero x → ∀ k (h : PosBound (add
    /// one (neg x)) k) a b, Nat.le a b → Within (seq (add (sumRange (fun j =>
    /// pow x j) b) (neg (sumRange (fun j => pow x j) a))) b) (add (seq (mul
    /// (inv (add one (neg x)) k h) (pow x a)) b) (natDivSucc 2 b))` —
    /// [`Self::geom_tail_within`]'s ordered-pair form `(m, add m n)` lifted to
    /// an arbitrary pair `(a, b)` constrained only by `a ≤ b`, via
    /// `Nat.le_dest` + `nat_rewrite_prop`: exactly the technique
    /// `series.rs::declare_sum_range_tail_within_le` uses to lift
    /// `sum_range_tail_within` the same way (reproduced in `geometric.rs`
    /// rather than reused, since that helper is private to `series.rs`).
    pub geom_tail_within_le: NameId,
    /// `CReal.geom_pair_within : ∀ x, le zero x → ∀ k (h : PosBound (add one
    /// (neg x)) k) a b, Nat.le a b → Within (sub (seq (sumRange (fun j => pow
    /// x j) b) b) (seq (sumRange (fun j => pow x j) a) a)) (add (add
    /// (modulus (shift b) b) (add (seq (mul (inv (add one (neg x)) k h) (pow
    /// x a)) b) (natDivSucc 2 b))) (modulus a (shift b)))` — the
    /// canonical-two-index normalization [`Self::geom_tail_within_le`] itself
    /// stops short of: a genuine bound on `seq (sumRange f b) b − seq
    /// (sumRange f a) a` (the shape [`Self::cauchy`] actually needs), not the
    /// shifted-sample shape `geom_tail_within_le` supplies.
    ///
    /// Built exactly like `series.rs`'s own `dominated_canonical_at` chains
    /// its four points `Y → X → W → Z` via `chain_within3` — **except** the
    /// middle leg here is [`Self::geom_tail_within_le`]'s own conclusion
    /// (needs no separately-witnessed `Cauchy` hypothesis, unlike the
    /// dominated-comparison-test's `g`), and the two outer legs are
    /// [`Self::regular`] applied to `sumRange f b` and `sumRange f a`
    /// themselves (a fact true of any `CReal`, so this needs no domination
    /// either). The bound still carries the undischarged sample `seq (mul
    /// (inv …) (pow x a)) b` from `geom_tail_within_le` rather than a fixed
    /// `natDivSucc`-shaped constant — see `geometric.rs`'s module
    /// documentation for exactly what remains (bounding that sample by a
    /// harmonic-shaped rational uniform in `a`, which needs a still-missing
    /// `pow`-vs-`natDivSucc` comparison lemma) and what does not (this
    /// theorem's own index bookkeeping, which is complete for the ordered
    /// pair `a ≤ b`; the `Nat.le_total` case split to remove that hypothesis
    /// is left unbuilt for the same reason `series.rs`'s own
    /// `sum_range_cauchy_dominated_ordered_normalized` leaves it to
    /// "whichever piece assembles `sum_range_cauchy_of_dominated` next" —
    /// `nat_prelude` has no `Nat.max`, so a single closed-form bound
    /// symmetric in `a`/`b` needs either that or a fresh `Within r q → 0 ≤ q`
    /// generic fact neither of which exists yet).
    pub geom_pair_within: NameId,
    /// `CReal.pow_le_pow_of_base_le : ∀ x y, le zero x → le x y → ∀ n,
    /// le (pow x n) (pow y n)` — monotonicity of `pow` in its **base**, for a
    /// fixed exponent, the comparison `geometric`'s own
    /// module documentation names as missing ("no lemma comparing `pow` at
    /// two different bases for the same exponent"). Induction on `n`: the
    /// base case is `le_refl one` up to `pow`'s own `ι`-reduction at `0`; the
    /// step derives `0 ≤ y` from `0 ≤ x ≤ y` via `le_trans`, multiplies the
    /// inductive hypothesis `pow x j ≤ pow y j` by the nonnegative `x` on the
    /// left (commuted into `pow`'s right-recursive shape via `mul_comm` +
    /// `le_congr`, exactly [`Self::pow_le_one`]'s own technique) to get
    /// `(pow x j)·x ≤ (pow y j)·x`, multiplies `x ≤ y` by the nonnegative
    /// `pow y j` on the left to get `(pow y j)·x ≤ (pow y j)·y`, and chains
    /// the two with `le_trans` to land on `pow x (succ j) ≤ pow y (succ j)`
    /// up to the same `ι`-reduction.
    pub pow_le_pow_of_base_le: NameId,
    /// `CReal.ofRat_pow : ∀ q n, Equiv (pow (ofRat q) n) (ofRat (Rat.pow q
    /// n))` — the embedding `ℚ ↪ ℝ` is a `Nat`-power homomorphism. Induction
    /// on `n`: both `CReal.pow` and `Rat.pow` share the identical
    /// `Nat.rec`-on-the-exponent shape (`pow _ 0 ≡ one`/`Rat.one`, `pow _
    /// (succ j) ≡ mul (pow _ j) _` with the fresh factor on the right), so
    /// neither `pow_zero`/`pow_succ` unfolding lemma is needed — the base and
    /// step terms below are accepted directly against the ι-reduced motive.
    /// The step chains [`Self::mul_congr`] (against the inductive hypothesis,
    /// on the left factor, [`Self::equiv_refl`] on the right) with
    /// [`Self::of_rat_mul`] (collapsing the product of two embeddings into
    /// the embedding of the product) via [`Self::equiv_trans`]. This is the
    /// missing piece `creal/geometric.rs`'s own module documentation names:
    /// there was no bridge from a `CReal.pow` at an embedded base to `Rat.pow`
    /// of the same rational, because `CReal.mul`'s sampling schedule is
    /// data-dependent and recursively self-referential across nested `pow`
    /// applications — this sidesteps that entirely by working at the
    /// `Equiv`/setoid level, never touching a sample.
    pub of_rat_pow: NameId,
    /// `CReal.pow_half_le_natDivSucc : ∀ n, le (pow (ofRat (natDivSucc 1 1))
    /// n) (ofRat (natDivSucc 1 n))` — geometric decay at base `1/2` dominates
    /// the harmonic rate, the estimate `creal/power.rs`'s own module
    /// documentation names as missing for `CReal.geom_cauchy`'s undischarged
    /// `seq Yₐ b` leaf (`creal/geometric.rs`'s `geom_pair_within`).
    ///
    /// Via [`Self::of_rat_pow`] (at `q := 1/2`) plus
    /// [`crate::rat_prelude::RatPrelude::bernoulli_harmonic_bound`] (at `x :=
    /// 1/2, t := 1`) transported back across it with [`Self::of_rat_le`] and
    /// [`Self::le_congr`]. `bernoulli_harmonic_bound`'s conclusion is stated
    /// against the inline `Nat.rec` companion `L t m := 1 + m·t`, not
    /// `natDivSucc` directly, so this also proves (privately, in
    /// `geometric.rs`) that `L Rat.one m` is exactly the whole-number
    /// embedding `natDivSucc (Nat.succ m) 0`, and cancels that positive
    /// factor from the resulting `L one m · pow (1/2) m ≤ 1` via
    /// `Rat.le_total`/`Rat.le_antisymm`/`Rat.mul_left_cancel_of_ne_zero` —
    /// never forming `Rat.inv`, matching `bernoulli_harmonic_bound`'s own
    /// design.
    pub pow_half_le_nat_div_succ: NameId,
    /// `CReal.pow_le_natDivSucc_of_lt : ∀ x, le zero x → lt x one →
    /// Exists (fun (K : Nat) => ∀ m, le (pow x m) (ofRat (natDivSucc K m)))`.
    ///
    /// The general-base generalization of [`Self::pow_half_le_nat_div_succ`]:
    /// geometric decay at ANY ratio `0 ≤ x < 1` (the strict bound supplied as
    /// `CReal.lt` data, never assumed) dominates *some* harmonic-shaped rate,
    /// entirely `CReal.inv`/`PosBound`-free. See `geometric.rs`'s
    /// `declare_pow_le_nat_div_succ_of_lt` for the derivation: the rational
    /// gap `q` from `lt x one` and the `Nat` witness `k` from
    /// [`Self::pos_bound_of_lt`] applied to `ofRat q` together bound a
    /// `CReal`-level companion to `Rat.bernoulli_harmonic_bound` (redone over
    /// `CReal` rather than reusing the `ℚ` original, since bridging a
    /// `Rat`-level bound back across a `CReal.pow` sample is exactly the open
    /// gap `rat_prelude/bernoulli.rs`'s own module doc names).
    pub pow_le_nat_div_succ_of_lt: NameId,
    /// `CReal.pow_le_natDivSucc_of_gap : ∀ x, le zero x → ∀ (q : Rat),
    /// le (add x (ofRat q)) one → ∀ (k3 : Nat), PosBound (ofRat q) k3 →
    /// ∀ m, le (pow x m) (ofRat (natDivSucc (Nat.succ k3) m))` — the **raw,
    /// non-existential** form of [`Self::pow_le_nat_div_succ_of_lt`].
    ///
    /// Same proof, same helpers (`creal_bernoulli_harmonic`,
    /// `k_relation_creal`, `creal_cancel_exact` in `creal/geometric.rs`),
    /// with the two `Exists` eliminations that theorem performs replaced by
    /// explicit parameters: the rational gap `q` it obtains from `lt x one`
    /// and the modulus `k3` it obtains from [`Self::pos_bound_of_lt`] are
    /// taken as data, and the `Exists.intro` on `K := Nat.succ k3` is
    /// dropped so the witness is visible in the statement.
    ///
    /// This is what a `Type`-valued consumer needs. `CReal.mk`'s regularity
    /// argument and `CReal.weierstrassMTest`'s `hcauchy` parameter both
    /// require a raw `(k, proof)` pair, and `Exists.rec` is `Prop`-only, so
    /// [`Self::pow_le_nat_div_succ_of_lt`]'s `∃ K, …` cannot be unwrapped to
    /// reach either. Note the hypothesis `lt x one` is **not** needed here —
    /// it existed only to produce `q` and `k3`.
    pub pow_le_nat_div_succ_of_gap: NameId,
    /// `CReal.geomYBoundRaw : ∀ x, le zero x → ∀ k (h : PosBound (add one
    /// (neg x)) k) (k1 : Nat), (∀ m, le (pow x m) (ofRat (natDivSucc k1
    /// m))) → ∀ a, le (mul (inv (add one (neg x)) k h) (pow x a)) (ofRat
    /// (natDivSucc (Nat.mul (Nat.succ k) k1) a))` — the **raw,
    /// non-existential** form of [`Self::geom_y_bound`], sharing its proof
    /// body (`geom_y_bound_leaf`, `creal/geometric.rs`) verbatim.
    ///
    /// [`Self::geom_y_bound`]'s `∃ K, …` is now derived FROM this by one
    /// `Exists.intro` after eliminating
    /// [`Self::pow_le_nat_div_succ_of_lt`]'s own existential, so the two
    /// cannot drift apart. As with
    /// [`Self::pow_le_nat_div_succ_of_gap`], the hypothesis `lt x one` is
    /// not needed: it existed only to manufacture `k1`.
    pub geom_y_bound_raw: NameId,
    /// `CReal.ratioDecayBound : ∀ f r, le zero r → (∀ n, le (f (Nat.succ n))
    /// (mul r (f n))) → ∀ n, le (f n) (mul (f Nat.zero) (pow r n))` — the
    /// ratio test's decay induction: a sequence shrinking by a factor `r` at
    /// each step (`f(n+1) ≤ r·f(n)`) stays under the geometric envelope
    /// `f(0)·rⁿ`. The correct orientation, established by counterexample: the
    /// reverse hypothesis `le (mul r (f n)) (f (Nat.succ n))` degenerates at
    /// `r := 0` to `0 ≤ f(n+1)`, satisfied by any nonnegative sequence
    /// including divergent ones (`f(n) := n+1`).
    ///
    /// Induction on `n`. Base case: `le (f 0) (mul (f 0) one)`, from
    /// `le_refl (f 0)` transported across `Equiv (f 0) (mul (f 0) one)`
    /// ([`Self::mul_one`], symmetrised) via [`Self::le_congr`] — the target
    /// type `mul (f 0) (pow r 0)` is defeq to `mul (f 0) one` since `pow`
    /// ι-reduces at `0`, so no further rewrite of the goal itself is needed.
    /// Step: multiplies the inductive hypothesis `f j ≤ f 0 · rʲ` by the
    /// nonnegative `r` on the left ([`Self::mul_le_mul_of_nonneg_left`]) to
    /// get `r·f(j) ≤ r·(f 0·rʲ)`, chains it below the decay hypothesis at `j`
    /// via [`Self::le_trans`], and transports the result across the
    /// three-step commute/associate chain `r·(f0·rʲ) ~ f0·(rʲ·r)`
    /// ([`Self::mul_assoc`]/[`Self::mul_comm`]/[`Self::mul_congr`]) via
    /// [`Self::le_congr`] — the target `f0·pow(r,succ j)` is defeq to
    /// `f0·(rʲ·r)` since `pow` ι-reduces its recursive factor on the right.
    pub ratio_decay_bound: NameId,
    /// `CReal.invLeOfPosBound : ∀ x k h, le (inv x k h) (ofNat (Nat.succ
    /// k))` — the inverse of a `PosBound`-witnessed positive real is bounded
    /// by a whole number computed from the very modulus that witnesses its
    /// positivity: `PosBound x k` says `1/(k+1) ≤ x`, so `x⁻¹ ≤ k+1`.
    ///
    /// Built without touching `inv`'s own representative (`creal/inverse.rs`
    /// is out of scope for this lane): from the `Rat`-level identity
    /// `(1/(k+1))·(k+1) = 1` ([`crate::RatPrelude::mul_inv_cancel`] at
    /// `q := natDivSucc 1 k` composed with
    /// [`crate::RatPrelude::inv_nat_div_succ`], never
    /// `Rat.normalize`/`Nat.gcd`), lifted to `Equiv (mul (ofRat (natDivSucc 1
    /// k)) (ofNat (Nat.succ k))) one` via [`Self::of_rat_mul`]. Multiplying
    /// `h : PosBound x k` (unfolds to `le (ofRat (natDivSucc 1 k)) x`) by the
    /// nonnegative `ofNat (Nat.succ k)` on the right gives `le (mul (ofRat
    /// (natDivSucc 1 k)) (ofNat (Nat.succ k))) (mul x (ofNat (Nat.succ
    /// k)))`, transported by the identity above into `le one (mul x (ofNat
    /// (Nat.succ k)))`, then into `le (mul x (inv x k h)) (mul x (ofNat
    /// (Nat.succ k)))` via [`Self::mul_inv_cancel`] (symmetrised) and
    /// [`Self::le_congr`], and finally cancelled by
    /// [`Self::le_of_mul_le_mul_left`] at the SAME witness `(k, h)` `inv`
    /// itself takes — no second modulus is invented.
    pub inv_le_of_pos_bound: NameId,
    /// `CReal.geomYBound : ∀ x, le zero x → lt x one → ∀ k (h : PosBound (add
    /// one (neg x)) k), ∃ K, ∀ a, le (mul (inv (add one (neg x)) k h) (pow x
    /// a)) (ofRat (natDivSucc K a))` — the general-base, symbolic-modulus
    /// generalization of [`Self::geom_half_inv_leaf_bound`] (concrete base
    /// `1/2`, `inv`-value pinned to the literal `2`).
    ///
    /// Combines [`Self::pow_le_nat_div_succ_of_lt`]'s harmonic witness `K1`
    /// (at `x`) with [`Self::inv_le_of_pos_bound`]'s `ofNat (succ k)` bound
    /// (at `add one (neg x)`, `k`, `h`) via two
    /// [`Self::mul_le_mul_of_nonneg_left`]/`_right` applications —
    /// `iv · xᵃ ≤ (succ k) · xᵃ ≤ (succ k) · natDivSucc K1 a` — then fuses the
    /// scaled bound into a single `natDivSucc` via `Rat.natDivSucc_mul`,
    /// giving the witness `K := (succ k)·K1`. `inv` and `PosBound` enter only
    /// through the hypothesis `h` this theorem already carries; nothing here
    /// invents a second modulus.
    pub geom_y_bound: NameId,
    /// `CReal.geomHalfInvLeafBound : ∀ a, le (mul (inv (add one (neg half)) 1
    /// h) (pow half a)) (ofRat (natDivSucc 2 a))`, `h` built internally (not
    /// a parameter) — the leaf [`Self::geom_pair_within`]'s own field doc
    /// names as undischarged (`seq Yₐ b`, `Yₐ := pow half a · inv (add one
    /// (neg half)) 1 h`), bounded in its full `CReal` form (`Yₐ ≤ 2/(a+1)`,
    /// not yet sampled at any index `b`).
    ///
    /// See `exponential.rs`'s module documentation for the derivation:
    /// `PosBound half 1` is `le_refl` applied to `half` itself (`half`'s own
    /// sample is the constant `1/2`); `PosBound (add one (neg half)) 1`
    /// transports it across `Equiv (add one (neg half)) half` via
    /// [`Self::le_congr`]; the `inv`-value itself is pinned to the rational
    /// constant `2` by cancelling `half` from both `Equiv (mul half (inv
    /// …)) one` ([`Self::mul_inv_cancel`]) and `Equiv (mul half (ofRat 2))
    /// one` (a `Rat`-level computation) via [`Self::le_of_mul_le_mul_left`]
    /// run in both directions plus [`Self::equiv_of_le_le`] — never via
    /// [`Self::inv_congr`]. Multiplying [`Self::pow_half_le_nat_div_succ`]
    /// through by that constant `2` closes it. `inv` enters only here, for
    /// this one concrete base; nothing downstream of this declaration
    /// touches `CReal.inv`/`PosBound` again.
    pub geom_half_inv_leaf_bound: NameId,
    /// `CReal.geomCauchyOrderedHalf : ∀ a b, Nat.le a b → Within (seq
    /// (sumRange (pow half) b) b − seq (sumRange (pow half) a) a)
    /// (natDivSucc 7 b + natDivSucc 7 a)`.
    ///
    /// The ordered-pair, fully-normalized geometric Cauchy bound at the
    /// concrete base `1/2`. [`Self::geom_half_inv_leaf_bound`] applied at
    /// index `b` and `Rat.le_of_sub_le`-converted bounds the leaf by
    /// `natDivSucc 2 a + natDivSucc 2 b`; two `Rat.natDivSucc_le_scaled`
    /// widenings retire the two `shift b` legs
    /// `Rat.natDivSucc_le_scaled` widenings retire the two `shift b` legs
    /// [`Self::geom_pair_within`] carries; and the seven resulting leaves
    /// (`2×natDivSucc 1 b`, `2×natDivSucc 2 b`, `1×natDivSucc 1 b`,
    /// `natDivSucc 2 a`, `natDivSucc 1 a`) fuse to `natDivSucc 7 b +
    /// natDivSucc 7 a` — `7` on the `b` side exactly, `3` padded up to `7` on
    /// the `a` side via one `Rat.natDivSucc_le_add_left`. `inv` enters only
    /// here, for this one concrete base; nothing downstream of this
    /// declaration touches `CReal.inv`/`PosBound` again.
    pub geom_cauchy_ordered_half: NameId,
    /// `CReal.geomCauchy : Cauchy (sumRange (fun n => pow half n))` —
    /// **`CReal.geom_cauchy`**, closing the goal `geometric.rs`'s own module
    /// documentation named as blocked (the blocker itself was stale — see
    /// `exponential.rs`'s module documentation for the correction).
    ///
    /// [`Self::geom_cauchy_ordered_half`]'s own bound is not symmetric in its
    /// two indices (the `b`-side leg costs more than the `a`-side one), so
    /// this eliminates the `Nat.le_total` disjunction — never branching on
    /// [`Self::le`] itself, which is undecidable — and calls
    /// `geom_cauchy_ordered_half` at whichever of `(m, n)`/`(n, m)` satisfies
    /// its own `a ≤ b` side condition, exactly mirroring
    /// `series.rs::declare_sum_range_cauchy_of_dominated`'s own case split
    /// (`within_symm` plus one `Rat.add_comm` rewrite in the `m ≤ n` branch,
    /// no rewrite needed in the `n ≤ m` branch), with the single fixed
    /// witness `K := 7` in place of that theorem's `k + 8`.
    pub geom_cauchy: NameId,
    /// `CReal.geomCauchyOfLtOrdered : ∀ x, le zero x → ∀ k (h : PosBound (add
    /// one (neg x)) k) (bigK : Nat) (hK : ∀ a, le (mul (inv (add one (neg
    /// x)) k h) (pow x a)) (ofRat (natDivSucc bigK a))) a b, Nat.le a b →
    /// Within (seq (sumRange (pow x) b) b − seq (sumRange (pow x) a) a)
    /// (natDivSucc ((bigK+1)+7) b + natDivSucc ((bigK+1)+7) a)` — the
    /// ordered-pair geometric Cauchy bound at a GENERAL ratio `x` and a
    /// symbolic leaf-bound witness `bigK`, mirroring
    /// [`Self::geom_cauchy_ordered_half`]'s derivation with
    /// [`Self::geom_y_bound`]'s general leaf bound in place of
    /// [`Self::geom_half_inv_leaf_bound`]'s literal `2` and the symbolic
    /// modulus `(bigK+1)+7` in place of the literal `7`. `(bigK+1)` fuses the
    /// `a`-side leaf with the regularity constant `natDivSucc 1 a`
    /// (`geometric.rs`'s own `fuse_same_index`); `7` on the `b` side is
    /// untouched from `geomCauchyOrderedHalf`'s own derivation (it never
    /// depended on the base). Since `bigK` is symbolic, the smaller side is
    /// padded up to the common target `(bigK+1)+7` via two
    /// `Rat.natDivSucc_le_add_left` applications plus one `Nat.add_comm`
    /// bridge, never via a literal coincidence like `geomCauchy`'s own
    /// `3+4=7`.
    pub geom_cauchy_of_lt_ordered: NameId,
    /// `CReal.geomCauchyOrderedOfGap : ∀ x, le zero x → ∀ (q : Rat), le
    /// (add x (ofRat q)) one → ∀ (k3 : Nat), PosBound (ofRat q) k3 → ∀ k (h
    /// : PosBound (add one (neg x)) k) a b, Nat.le a b → Within (seq
    /// (sumRange (pow x) b) b − seq (sumRange (pow x) a) a) (natDivSucc N
    /// b + natDivSucc N a)`, with `N := ((Nat.succ k * Nat.succ k3) + 1) +
    /// 7` — **the raw, non-existential ordered geometric Cauchy witness at
    /// an ARBITRARY ratio**, and the point of this family.
    ///
    /// Exactly one such witness existed before this
    /// (`CReal.geomCauchyOrderedHalf`, `exponential.rs`), hardcoded to the
    /// literal ratio `1/2` through
    /// [`Self::geom_half_inv_leaf_bound`]'s `inv`-cancellation at that one
    /// value. Every `Type`-valued consumer — `CReal.mk`, and
    /// `CReal.weierstrassMTest`'s `hcauchy` argument — needs a raw `(k,
    /// proof)` pair rather than a `Prop`-wrapped [`Self::cauchy`], and the
    /// general-ratio machinery ([`Self::geom_cauchy_of_lt`],
    /// [`Self::geom_y_bound`], [`Self::pow_le_nat_div_succ_of_lt`]) is
    /// `Exists`-wrapped all the way down, so it answers "a rate exists"
    /// (`Prop`) and never "here it is" (data).
    ///
    /// It is a pure composition, no new arithmetic: `hK1 :=
    /// [`Self::pow_le_nat_div_succ_of_gap`]` at `(q, k3)` feeds
    /// [`Self::geom_y_bound_raw`], whose conclusion is exactly
    /// [`Self::geom_cauchy_of_lt_ordered`]'s already-raw `hK` parameter.
    /// The ratio-specific work a caller must supply is only rational: the
    /// gap `q` with `x + q ≤ 1`, and two `PosBound` moduli.
    pub geom_cauchy_ordered_of_gap: NameId,
    /// `CReal.geomCauchyOrdered16Over25 : ∀ a b, Nat.le a b → Within (seq
    /// (sumRange (pow (ofRat (natDivSucc 16 24))) b) b − seq (sumRange (pow
    /// (ofRat (natDivSucc 16 24))) a) a) (natDivSucc N b + natDivSucc N a)`,
    /// `N := ((25*25)+1)+7` — [`Self::geom_cauchy_ordered_of_gap`]
    /// instantiated at the concrete ratio `16/25`, the **first raw geometric
    /// Cauchy witness in this kernel at a ratio other than `1/2`**.
    ///
    /// `16/25 = (4/5)² = ((8/5)/2)²`, which is the ratio
    /// `creal/trig_fn.rs`'s pointwise bound `abs (cosFnTerm k x) ≤
    /// 2·((R/2)²)^k` produces at `R := 8/5 = 1.6`. `1.6 > 1.5708`, so this
    /// ratio *does* clear cosine's first zero; the commonly-quoted
    /// alternative `9/16` (`R := 3/2`) does **not**, since `1.5 < 1.5708`.
    ///
    /// It is also genuinely outside the reach of the base-`1/2` machinery:
    /// `16/25 > 1/2`, and [`Self::pow_le_pow_of_base_le`] compares upward,
    /// so no amount of base monotonicity puts `(16/25)^k` under `(1/2)^k`.
    ///
    /// See `geometric.rs::declare_geom_cauchy_ordered_16_over_25` for how the
    /// three rational obligations are discharged at one common denominator.
    pub geom_cauchy_ordered_16_over_25: NameId,
    /// `CReal.geomCauchyBodyOfGap : ∀ x, le zero x → ∀ (q : Rat), le (add x
    /// (ofRat q)) one → ∀ (k3 : Nat), PosBound (ofRat q) k3 → ∀ k (h :
    /// PosBound (add one (neg x)) k) m n, Within (seq (sumRange (pow x) m) m
    /// − seq (sumRange (pow x) n) n) (natDivSucc N m + natDivSucc N n)`, `N`
    /// as in [`Self::geom_cauchy_ordered_of_gap`] — that theorem with the `m
    /// ≤ n` side condition removed by `Nat.le_total`, and **still raw**.
    ///
    /// This is the shape `series.rs::sum_range_cauchy_body` builds, which is
    /// exactly `CReal.weierstrassMTest`'s `hcauchy` parameter and exactly
    /// what `CReal.mk` needs for a regularity argument. It is what
    /// [`Self::geom_cauchy`] proves internally and then throws away: that
    /// theorem's last step is an `Exists.intro` into [`Self::cauchy`], a
    /// `Prop`, and `Exists.rec` cannot eliminate a `Prop` into a `Type`.
    /// Stopping one step earlier is the whole difference.
    pub geom_cauchy_body_of_gap: NameId,
    /// `CReal.geomCauchyBody16Over25 : ∀ m n, Within (seq (sumRange (pow
    /// (ofRat (natDivSucc 16 24))) m) m − seq (sumRange (pow (ofRat
    /// (natDivSucc 16 24))) n) n) (natDivSucc N m + natDivSucc N n)`,
    /// `N := ((25*25)+1)+7` — [`Self::geom_cauchy_body_of_gap`] at the
    /// concrete ratio `16/25`.
    ///
    /// **The first `weierstrassMTest`-shaped raw Cauchy witness in this
    /// kernel at a ratio other than `1/2`.** See
    /// [`Self::geom_cauchy_ordered_16_over_25`] for why `16/25` and not
    /// `9/16`.
    pub geom_cauchy_body_16_over_25: NameId,
    /// `CReal.geomCauchyOfLt : ∀ x, le zero x → lt x one → ∀ k (h : PosBound
    /// (add one (neg x)) k), Cauchy (sumRange (fun n => pow x n))` —
    /// geometric-series Cauchyness at a GENERAL ratio `0 ≤ x < 1`, the
    /// generalization of [`Self::geom_cauchy`] (concrete base `1/2`) needed
    /// for Chapter 22–23's ratio test.
    ///
    /// Eliminates [`Self::geom_y_bound`]'s outer existential `∃ K, …` to
    /// obtain a concrete-but-symbolic witness `(bigK, hK)`, then runs the
    /// same `Nat.le_total` case split [`Self::geom_cauchy`] runs against
    /// [`Self::geom_cauchy_ordered_half`] — here against
    /// [`Self::geom_cauchy_of_lt_ordered`] — with the witness `(bigK+1)+7`
    /// (a function of `bigK`, never simplified to a literal) in place of that
    /// theorem's fixed `K := 7`.
    pub geom_cauchy_of_lt: NameId,
    /// `creal/ratio_test.rs`'s own 2 names, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.ratio_test.geom_scaled_cauchy_of_lt` and documented in
    /// [`RatioTestNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub ratio_test: RatioTestNames,
    /// `CReal.one_le_pow_of_one_le : ∀ x, le one x → ∀ n, le one (pow x n)` —
    /// the mirror of [`Self::pow_le_one`]: powers of a base at least `1` stay
    /// at least `1`. Induction on `n`, and simpler than `pow_le_one`'s own
    /// proof: `pow`'s recursive factor `mul (pow x j) x` already has the
    /// accumulator on the **left**, matching [`Self::mul_le_mul_of_nonneg_left`]'s
    /// `c := pow x j` slot directly, so no final `mul_comm` is needed.
    pub one_le_pow_of_one_le: NameId,
    /// `CReal.pow_le_pow_of_one_le : ∀ x, le one x → ∀ n, le (pow x n) (pow x
    /// (Nat.succ n))` — the mirror of [`Self::pow_le_pow_of_le_one`]: the
    /// powers are non-decreasing when the base is at least `1`. Not an
    /// induction, one step for an arbitrary fixed `n`, exactly like its
    /// mirror — and needs only the one hypothesis `1 ≤ x`, since `0 ≤ x`
    /// ([`Self::pow_nonneg`]'s own hypothesis) follows from it via
    /// [`Self::zero_lt_one`] and [`Self::le_trans`] rather than being taken
    /// as a separate parameter.
    pub pow_le_pow_of_one_le: NameId,
    /// `CReal.pow_pos : ∀ x, lt zero x → ∀ n, lt zero (pow x n)` — strict
    /// positivity is preserved by `pow`. Induction on `n`: the base case is
    /// [`Self::zero_lt_one`] up to `pow`'s ι-reduction, the step is
    /// [`Self::mul_pos`] applied to the inductive hypothesis and the outer
    /// `0 < x`.
    pub pow_pos: NameId,
    /// `CReal.pow_succ_lt_one : ∀ x, le zero x → lt x one → ∀ m, lt (pow x
    /// (Nat.succ m)) one` — **the strict half of [`Self::pow_le_one`]** that
    /// file lacked: a base strictly below `1` stays strictly below `1` at
    /// every positive power (stated over `Nat.succ m` rather than a bare `n`
    /// with a separate `0 < n` hypothesis, since `pow x 0 ≡ one` is not `<
    /// one` and every downstream use already has a successor in hand).
    ///
    /// Induction on `m`, and structurally [`Self::pow_le_one`]'s own proof
    /// with the closing step swapped: base case rewrites `mul one x ~ x`
    /// along the hypothesis `x < one` via [`Self::lt_congr`]; the step
    /// multiplies the *strict* inductive hypothesis `pow x (succ j) < one`
    /// by `x ≤ one` on the right
    /// ([`Self::mul_le_mul_of_nonneg_left`] at `c := pow x (succ j)`,
    /// nonnegative via [`Self::pow_nonneg`], giving `mul (pow x (succ j)) x ≤
    /// mul (pow x (succ j)) one ~ pow x (succ j)`) and chains that `≤` against
    /// the strict IH with [`Self::lt_of_le_of_lt`] — no [`Self::mul_pos`], no
    /// rational-gap algebra, needed anywhere.
    pub pow_succ_lt_one: NameId,
    /// `CReal.pow_succ_gt_one : ∀ x, lt one x → ∀ m, lt one (pow x (Nat.succ
    /// m))` — the mirror of [`Self::pow_succ_lt_one`]: a base strictly above
    /// `1` stays strictly above `1` at every positive power. Same proof shape
    /// with the inequalities flipped and [`Self::lt_of_lt_of_le`] closing the
    /// step instead of [`Self::lt_of_le_of_lt`]; `0 ≤ x` is derived from `1 <
    /// x` rather than taken as a hypothesis, exactly as in
    /// [`Self::pow_le_pow_of_one_le`].
    pub pow_succ_gt_one: NameId,
    /// `CReal.not_apart_one_of_pow_succ_eq_one : ∀ x, le zero x → ∀ m, Equiv
    /// (pow x (Nat.succ m)) one → Not (Apart x one)`.
    ///
    /// **This is the honest shape of the inversion the module doc's
    /// "obstruction" section names, not the `Equiv x one` a reader might
    /// expect.** The route: assume `Apart x one`, i.e. `lt x one ∨ lt one x`
    /// ([`Self::apart`]'s own definition, consumed by `Or`-elimination with
    /// no case split manufactured from nothing — the disjunction is
    /// *given*). In the first branch, [`Self::pow_succ_lt_one`] turns `x <
    /// one` into `pow x (succ m) < one`; the hypothesis `Equiv (pow x (succ
    /// m)) one` gives the opposite `le one (pow x (succ m))`
    /// ([`Self::le_of_equiv`] on the symmetrised equivalence); chaining the
    /// two with [`Self::lt_of_le_of_lt`] produces `lt one one`, refuted by
    /// [`Self::lt_irrefl`]. The second branch mirrors this with
    /// [`Self::pow_succ_gt_one`] and [`Self::lt_of_lt_of_le`].
    ///
    /// **Why this cannot be strengthened to `Equiv x one` here**:
    /// [`Self::apart`]'s own doc block states the wall directly — `Apart x y`
    /// is *strictly stronger* than `Not (Equiv x y)`, and the converse
    /// (tightness, `Not (Apart x y) → Equiv x y`) is Markov's principle,
    /// "neither proved nor assumed" anywhere in this development. This
    /// theorem's conclusion is exactly `Not (Apart x one)` — tightness is
    /// the one missing step from here to `Equiv x one`, and it is a
    /// genuinely different (classically-flavoured) proposition, not a
    /// missing lemma this file failed to look up.
    pub not_apart_one_of_pow_succ_eq_one: NameId,

    // --- the derivative, on an interval (creal/derivative.rs) ----------------
    /// `CReal.HasDerivativeOn (F F' : CReal -> CReal) (a b : CReal) : Type :=
    /// mk (modulus : Nat -> Nat) (spec : ...)` — the FIRST derivative in this
    /// kernel. Bishop's UNIFORM differentiability on a closed interval, one
    /// parameter over [`Self::uniformly_continuous_on`]'s own shape (`F'` is
    /// now part of the family, so there are four leading parameters rather
    /// than three); see that field's doc for why the modulus has to be a
    /// `Type`-valued data field rather than a `Prop`-level `forall e, exists
    /// delta, ...`, which applies here verbatim.
    ///
    /// `spec : forall (e : Nat) (x y : CReal), le a x -> le x b -> le a y ->
    /// le y b -> le (abs (add y (neg x))) (ofRat (natDivSucc 1 (modulus e)))
    /// -> le (abs (add (add (F y) (neg (F x))) (neg (mul (F' x) (add y (neg
    /// x)))))) (mul (ofRat (natDivSucc 1 e)) (abs (add y (neg x))))` —
    /// `|F y - F x - F' x * (y - x)| <= (1/(e+1)) * |y - x|` whenever `|y -
    /// x|` is within the modulus's own threshold. The four range hypotheses
    /// are [`Self::uniformly_continuous_on`]'s own, reused verbatim rather
    /// than a bundled interval predicate (there is none in this file). The
    /// bound is `CReal`-valued (a product, not a rational constant), so this
    /// is not [`Self::within`] (which bounds a `Rat`).
    pub has_derivative_on: NameId,
    /// `HasDerivativeOn.mk`, the one constructor.
    pub hd_mk: NameId,
    /// `HasDerivativeOn.rec`, the kernel-generated recursor (four leading
    /// parameters `F F' a b`).
    pub hd_rec: NameId,
    /// `HasDerivativeOn.modulus : forall F F' a b, HasDerivativeOn F F' a b
    /// -> Nat -> Nat` — the data field, by large elimination,
    /// [`Self::uc_modulus`]'s own shape one parameter over.
    pub hd_modulus: NameId,
    /// `HasDerivativeOn.spec` — the Prop-valued field, projected the same
    /// shape [`Self::uc_spec`] uses: the motive at a witness `u` mentions
    /// `HasDerivativeOn.modulus F F' a b u`, not a fresh variable.
    pub hd_spec: NameId,
    /// `CReal.hasDerivative_const : forall c a b, HasDerivativeOn (fun _ =>
    /// c) (fun _ => zero) a b` — the error term `c - c - 0*(y-x)` is
    /// `Equiv`-zero unconditionally (`add_neg` plus `mul`-by-zero), so any
    /// modulus works (`fun _ => 0` is used), mirroring
    /// [`Self::uniformly_continuous_const`].
    pub has_derivative_const: NameId,
    /// `CReal.hasDerivative_id : forall a b, HasDerivativeOn (fun r => r)
    /// (fun _ => one) a b` — the error term `(y-x) - 1*(y-x)` is
    /// `Equiv`-zero unconditionally (`mul_one`/`mul_comm`), any modulus
    /// works.
    ///
    /// The sum rule (`hasDerivative_add`, [`Self::has_derivative_add`]),
    /// `hasDerivative_neg` ([`Self::has_derivative_neg`]),
    /// `hasDerivative_smul` ([`Self::has_derivative_smul`]) and
    /// `hasDerivative_sub` ([`Self::has_derivative_sub`]) are all landed —
    /// see `creal/derivative.rs`'s own module documentation. **Still not
    /// landed**: the product rule, which needs a genuinely three-way
    /// (unequally weighted) accuracy fusion beyond what `smul`/`add` built,
    /// plus wiring `UniformlyContinuousOn`'s own modulus/spec into this file
    /// — see the module documentation's corrected, numerically re-verified
    /// error decomposition.
    pub has_derivative_id: NameId,
    /// `CReal.hasDerivative_sq : forall a b, HasDerivativeOn (fun r => mul r
    /// r) (fun x => add x x) a b` — the first **nonlinear** derivative in
    /// this kernel. The error term is `Equiv`-exactly `(y-x)*(y-x)` (not
    /// merely zero), so the modulus is the identity and the bound closes via
    /// a from-scratch "difference of squares" toolkit
    /// (`creal/derivative.rs`'s `diff_of_squares`/`sq_le_abs_sq`) built for
    /// this slice, since none of it existed in [`CRealPrelude`] beforehand.
    pub has_derivative_sq: NameId,
    /// `CReal.hasDerivative_neg : forall F F' a b, HasDerivativeOn F F' a b
    /// -> HasDerivativeOn (fun r => neg (F r)) (fun x => neg (F' x)) a b` —
    /// `neg`'s error term is exactly `neg` of `F`'s own error term (the
    /// scaling factor is `-1`, so no rescaled modulus is needed: the SAME
    /// modulus `F` already carries works unchanged), via
    /// `creal/derivative.rs`'s `neg_mul_equiv_left`/`double_neg`/
    /// `neg_add_distrib` ring toolkit plus a new general
    /// `le_abs_neg_of_le_abs` combinator.
    pub has_derivative_neg: NameId,
    /// `CReal.hasDerivative_add : forall F F' G G' a b, HasDerivativeOn F F'
    /// a b -> HasDerivativeOn G G' a b -> HasDerivativeOn (fun r => add (F
    /// r) (G r)) (fun x => add (F' x) (G' x)) a b` — **the sum rule**,
    /// unblocked by `Rat.natDivSucc_antitone`
    /// ([`RatPrelude::nat_div_succ_antitone`]) after months on that one
    /// missing lemma: the combined modulus is `fun e => mF (2e+1) + mG
    /// (2e+1)` (`Nat.add`, not `max` — `nat_prelude` has no `Nat.max`, and
    /// `Nat.le_add_right`/`Nat.add_comm` give both `<=` directions just as
    /// well), antitonicity reads the combined hypothesis back down to each
    /// sub-derivative's own modulus at `2e+1`, and
    /// `Rat.natDivSucc_add`/`Rat.natDivSucc_halve` fuse the two `1/(2e+2)`
    /// error bounds back into the single target `1/(e+1)` — the "each error
    /// bounded by HALF the target" arithmetic the module documentation
    /// verifies against `natDivSucc`'s actual definition.
    pub has_derivative_add: NameId,
    /// `CReal.abs_mul_le_of_bounds : ∀ c t B b, le (abs c) B → le (abs t) b →
    /// le (abs (mul c t)) (mul B b)` — the two-variable product-of-bounds
    /// lemma `creal/derivative.rs`'s own module documentation identifies as
    /// the single blocker standing between this kernel and both
    /// `hasDerivative_smul` and `hasDerivative_mul` (the product rule).
    ///
    /// `0 ≤ B` and `0 ≤ b` are **not** separate hypotheses — `abs_nonneg`
    /// plus `le_trans` gets both for free from `le (abs c) B` and
    /// `le (abs t) b`, so requiring them would only weaken the statement.
    ///
    /// Closed case-split-free (`CReal.le` is undecidable, so nothing here
    /// ever branches on a real comparison) via two nonneg-product identities,
    /// one per direction: `2·(B·b − c·t) = (B−c)·(b+t) + (B+c)·(b−t)` and,
    /// applying the same fact at `c := neg c`, the mirror identity for the
    /// lower bound. The factor of `2` is discharged by
    /// `creal/derivative.rs::nonneg_of_double_nonneg`, which multiplies
    /// through by the literal `CReal.ofRat (Rat.natDivSucc 1 1)` rather than
    /// deciding any sign.
    pub abs_mul_le_of_bounds: NameId,
    /// `CReal.BoundedOn (h : CReal → CReal) (a b : CReal) (k : Nat) : Prop :=
    /// ∀ z, le a z → le z b → le (abs (h z)) (ofRat (natDivSucc (Nat.succ k)
    /// 0))` — a transparent `Definition`, naming `creal/derivative.rs`'s own
    /// private `bounded_on_ty` helper (the inline shape
    /// [`Self::has_derivative_mul`]'s and [`Self::has_derivative_cube`]'s own
    /// `hbf`/`hbg`/`hbgp` hypotheses already use) rather than restating it.
    ///
    /// `Regular`, not `Opaque`, so it stays defeq to `bounded_on_ty`'s inline
    /// form and a closure theorem stated over it can still be applied at
    /// those two theorems' own existing call sites without editing their
    /// statements — see [`Self::bounded_on_unfold`] for the confirmation and
    /// [`Self::bounded_on_mul`] for a proof that exercises it.
    pub bounded_on: NameId,
    /// `CReal.bounded_on_unfold : ∀ h a b k, BoundedOn h a b k → ∀ z, le a z
    /// → le z b → le (abs (h z)) (ofRat (natDivSucc (Nat.succ k) 0))`, proved
    /// by `fun h a b k hyp => hyp` — the identity function on `hyp`, ascribed
    /// a conclusion type stated in `bounded_on_ty`'s own raw, unfolded shape.
    /// This typechecks **only** because [`Self::bounded_on`] is definitionally
    /// equal to that shape by one delta step; it exercises nothing else, so a
    /// failure here would isolate a defeq break from every other reason
    /// [`Self::bounded_on_mul`] might fail to build.
    pub bounded_on_unfold: NameId,
    /// `CReal.bounded_on_mul : ∀ F G a b k1 k2, BoundedOn F a b k1 →
    /// BoundedOn G a b k2 → BoundedOn (fun z => mul (F z) (G z)) a b
    /// (Nat.add (Nat.add (Nat.mul k1 k2) k1) k2)` — the product of two
    /// functions bounded on `[a,b]` is bounded on `[a,b]`.
    ///
    /// The combined bound `k3 := k1·k2 + k1 + k2` is chosen so that `Nat.succ
    /// k3 = Nat.succ k1 · Nat.succ k2` **exactly**, with no `Nat.sub`
    /// anywhere: [`RatPrelude::nat_div_succ_mul`] folds `natDivSucc (succ k1)
    /// 0 · natDivSucc (succ k2) 0` to `natDivSucc (succ k1 · succ k2) 0` in
    /// one step (the general two-index form
    /// [`Self::has_derivative_mul`]'s own `fold_index0_first` needs is not
    /// needed here — both factors already carry index `0`), so the only
    /// remaining work is the `Nat` identity above, closed by `succ_mul` /
    /// `mul_succ` / `add_succ` (defining equations, not a new lemma).
    ///
    /// The proof applies `hF`/`hG` (typed `BoundedOn F a b k1` / `BoundedOn G
    /// a b k2`) directly to a point `z` and its two range proofs, the exact
    /// shape [`Self::has_derivative_mul`]'s own `hbf`/`hbg`/`hbgp` are
    /// applied at — the confirmation [`Self::bounded_on_unfold`] gives in
    /// isolation, exercised here inside a real closure proof.
    pub bounded_on_mul: NameId,
    /// `CReal.bounded_on_add : ∀ F G a b k1 k2, BoundedOn F a b k1 →
    /// BoundedOn G a b k2 → BoundedOn (fun z => add (F z) (G z)) a b
    /// (Nat.add k1 (Nat.succ k2))` — the sum of two functions bounded on
    /// `[a,b]` is bounded on `[a,b]`.
    ///
    /// Simpler than [`Self::bounded_on_mul`]: [`RatPrelude::nat_div_succ_add`]
    /// folds `natDivSucc (succ k1) 0 + natDivSucc (succ k2) 0` to `natDivSucc
    /// (succ k1 + succ k2) 0` directly (no index-`0`-only restriction the way
    /// [`RatPrelude::nat_div_succ_mul`] has), and the combined bound `k3 :=
    /// k1 + succ k2` is chosen so `succ k1 + succ k2 = succ k3` by
    /// `Nat.succ_add` alone — no `mul_succ`/`add_succ` dance. The magnitude
    /// step reuses `creal/derivative.rs`'s own private `abs_add_le` helper
    /// (`|F z + G z| ≤ |F z| + |G z|`, already built for
    /// [`Self::has_derivative_add`]) chained against the two given bounds via
    /// `add_le_add` and `le_trans`, not [`Self::abs_mul_le_of_bounds`].
    ///
    /// This is the piece `creal/derivative.rs`'s own module documentation
    /// identifies as still missing for `hasDerivative_pow` at general `n`
    /// beyond [`Self::bounded_on_mul`]: the product rule's derivative term
    /// `F'(x)·G(x) + F(x)·G'(x)` is a **sum**, so advancing the induction
    /// `pow (n+1) = id · pow n` needs boundedness of that sum at every step,
    /// not just of `pow n` itself.
    pub bounded_on_add: NameId,
    /// `CReal.hasDerivative_smul : ∀ c F F' a b, HasDerivativeOn F F' a b →
    /// ∀ (k : Nat), le (abs c) (ofRat (natDivSucc (Nat.succ k) 0)) →
    /// HasDerivativeOn (fun r => mul c (F r)) (fun x => mul c (F' x)) a b` —
    /// **the scalar-multiple rule**, unblocked by
    /// [`Self::abs_mul_le_of_bounds`]. The modulus is `fun e => mF ((k+1)·e +
    /// k)` (F's own modulus, read at the rescaled accuracy; no combination,
    /// so no antitonicity is needed — the rescaled hypothesis at `e` is
    /// definitionally F's own hypothesis at `e'`). The output bound needs
    /// `abs_mul_le_of_bounds` (`|c|<=k+1`, `|error_F|<=1/(e'+1)·|y-x|` gives
    /// `|c·error_F| <= (k+1)·(1/(e'+1))·|y-x|`) plus the rational identity
    /// `(k+1)·(1/(e'+1)) = 1/(e+1)`, via `Rat.natDivSucc_mul` (folding the
    /// literal product `(k+1)·1`) and `Rat.natDivSucc_scale` (reading the
    /// deep factor back to `e`) — `k+1` carries a real `Nat.mul _ 1`, closed
    /// by `Nat.mul_one` and transported through `natDivSucc`'s numerator via
    /// `nat_eq_to_rat` (private to `rat_prelude::ops`) rather than relying on
    /// any definitional reduction (`Nat.mul` is stuck on a free second
    /// argument, so there is none to rely on).
    pub has_derivative_smul: NameId,
    /// `CReal.hasDerivative_sub : ∀ F F' G G' a b, HasDerivativeOn F F' a b →
    /// HasDerivativeOn G G' a b → HasDerivativeOn (fun r => add (F r) (neg
    /// (G r))) (fun x => add (F' x) (neg (G' x))) a b` — cheap composition of
    /// [`Self::has_derivative_neg`] and [`Self::has_derivative_add`]: no new
    /// ring algebra, just `hasDerivative_add F (neg∘G) hf (hasDerivative_neg
    /// G hg)`.
    pub has_derivative_sub: NameId,
    /// `CReal.hasDerivative_mul : ∀ F F' G G' a b, HasDerivativeOn F F' a b →
    /// HasDerivativeOn G G' a b → UniformlyContinuousOn F a b → ∀ (k1 k2 k3 :
    /// Nat), (∀ z, le a z → le z b → le (abs (F z)) (ofRat (natDivSucc
    /// (succ k1) 0))) → (∀ z, le a z → le z b → le (abs (G z)) (ofRat
    /// (natDivSucc (succ k2) 0))) → (∀ z, le a z → le z b → le (abs (G' z))
    /// (ofRat (natDivSucc (succ k3) 0))) → HasDerivativeOn (fun r => mul (F
    /// r) (G r)) (fun x => add (mul (F' x) (G x)) (mul (F x) (G' x))) a b` --
    /// **the product rule**, closed by three EXPLICIT magnitude-bound
    /// hypotheses (on `F`, `G` and `G'`, none derived) plus uniform
    /// continuity of `F`, unblocked by a genuinely three-way accuracy split
    /// (`Rat.natDivSucc_add` twice plus `Rat.natDivSucc_scale` at `c := 2`,
    /// `hasDerivative_add`'s two-way `natDivSucc_halve` fuse one step
    /// deeper) and a three-source combined modulus (`hasDerivative_add`'s
    /// own `Nat.add`/antitonicity combination, extended to three sources).
    /// See `creal/derivative.rs`'s module documentation for the corrected,
    /// numerically re-verified error decomposition this closes.
    pub has_derivative_mul: NameId,
    /// `CReal.hasDerivative_congr : ∀ F F' a b, HasDerivativeOn F F' a b →
    /// ∀ G G', (∀ x, le a x → le x b → Equiv (G x) (F x)) →
    /// (∀ x, le a x → le x b → Equiv (G' x) (F' x)) →
    /// HasDerivativeOn G G' a b` — transport a derivative along pointwise
    /// `Equiv` **on the interval only**.
    ///
    /// `HasDerivativeOn.spec`'s own type guards every occurrence of
    /// `F x`/`F y`/`F' x` in its conclusion behind the SAME range hypotheses
    /// (`le a x`, `le x b`, `le a y`, `le y b`) the caller must already supply
    /// to invoke `spec` at all, so agreement need only hold ON `[a,b]` —
    /// off-interval agreement is neither needed nor assumed. Reuses `F`'s own
    /// modulus verbatim; `abs_le_of_equiv` carries `F`'s own bound across.
    ///
    /// A constructive derivative is **not unique as a function**, only up to
    /// pointwise `Equiv` on the interval, so without this two developments
    /// producing the "same" derivative in different syntactic forms cannot be
    /// connected at all.
    pub has_derivative_congr: NameId,
    /// `CReal.hasDerivative_pow_two : ∀ a b,
    /// HasDerivativeOn (fun r => pow r 2) (fun x => add x x) a b` — `pow r 2`
    /// ι-reduces to `mul (mul one r) r`, `Equiv`-equal to `mul r r`, so
    /// [`Self::has_derivative_congr`] transports [`Self::has_derivative_sq`]'s
    /// witness across that one identity with the derivative side reused
    /// verbatim. **The cross-check this development wanted**: had the general
    /// shape not matched `hasDerivative_sq` at `n = 2`, one of the two would be
    /// wrong.
    pub has_derivative_pow_two: NameId,
    /// `CReal.hasDerivative_cube : ∀ a b k1 k2 k3,
    /// (∀ z, le a z → le z b → le (abs z) (ofRat (natDivSucc (succ k1) 0))) →
    /// (∀ z, le a z → le z b → le (abs (mul z z)) (ofRat (natDivSucc (succ
    /// k2) 0))) → (∀ z, le a z → le z b → le (abs (add z z)) (ofRat
    /// (natDivSucc (succ k3) 0))) → HasDerivativeOn (fun r => mul r (mul r
    /// r)) (fun x => add (mul one (mul x x)) (mul x (add x x))) a b` — the
    /// cube rule, built with **zero new algebra**: `r*(r*r)` is exactly
    /// `id(r) * sq(r)`, so this is [`Self::has_derivative_mul`] applied
    /// directly to [`Self::has_derivative_id`] and [`Self::has_derivative_sq`],
    /// with `CReal.uniformly_continuous_id` supplying the continuity
    /// hypothesis the product rule's own third term needs.
    ///
    /// The three magnitude bounds (on `id`, on `sq`, and on `sq`'s own
    /// derivative `fun x => x+x`) are three INDEPENDENT caller-supplied
    /// hypotheses, matching `hasDerivative_mul`'s own three-independent-
    /// bounds shape exactly — deliberately **not** derived from one another
    /// via a single interval bound. Folding them into one would need a rational
    /// identity of the shape `natDivSucc(m,0) * natDivSucc(n,0) =
    /// natDivSucc(m*n,0)`, which is not established anywhere in this prelude
    /// (see `creal/derivative.rs`'s module documentation for what closing a
    /// comparably-shaped gap — `Rat.natDivSucc` antitone in its index —
    /// actually cost the sum rule); avoiding that gap by taking three
    /// independent hypotheses is what keeps this cheap.
    pub has_derivative_cube: NameId,
    /// `CReal.hasDerivative_pow : ∀ a b k1, BoundedOn (fun r => r) a b k1 →
    /// ∀ (kb kd : Nat → Nat),
    ///   (∀ n, BoundedOn (fun r => pow r n) a b (kb n)) →
    ///   (∀ n, BoundedOn (fun x => mul (ofNat (Nat.succ n)) (pow x n)) a b
    ///     (kd n)) →
    ///   ∀ n, HasDerivativeOn (fun r => pow r (Nat.succ n))
    ///     (fun x => mul (ofNat (Nat.succ n)) (pow x n)) a b` — the general
    /// power rule, by induction on `n` at exponent `succ n` (never `n - 1`:
    /// `Nat.sub` is truncated and banned in an index). See
    /// `creal/derivative.rs::declare_has_derivative_pow`'s own doc comment for
    /// why the exponent is `succ n`, why the induction commutes each product
    /// before calling [`Self::has_derivative_mul`], and why boundedness is
    /// two explicit Skolem functions rather than a derived fact.
    pub has_derivative_pow: NameId,
    /// `CReal.hasDerivative_chain : ∀ F F' G G' a b,
    ///   HasDerivativeOn F F' a b → HasDerivativeOn G G' a b →
    ///   UniformlyContinuousOn F a b →
    ///   (∀ z, le a z → le z b → le a (F z)) →
    ///   (∀ z, le a z → le z b → le (F z) b) →
    ///   ∀ k1 k2, BoundedOn F' a b k1 → BoundedOn G' a b k2 →
    ///   HasDerivativeOn (fun r => G (F r)) (fun x => mul (G' (F x)) (F' x))
    ///   a b` — the chain rule. The domain question is settled by the two
    /// self-map hypotheses (`∀ z, ... → le a (F z)` / `... → le (F z) b`),
    /// in [`Self::bounded_on`]'s own two-Π shape rather than a bundled `And`
    /// or a second interval for `G` — see
    /// `creal/derivative.rs::declare_has_derivative_chain`'s own doc comment
    /// for what that choice costs and why. The two-level modulus composition
    /// (`UniformlyContinuousOn F a b`'s own modulus applied to `G`'s
    /// modulus, not to a `Nat` literal) is what the scouting report flagged
    /// as genuinely new; the error term itself telescopes EXACTLY (`E =
    /// [G's own error at (F x, F y)] + G'(F x) * [F's own error at (x,y)]`,
    /// no ring expansion), unlike the product rule.
    pub has_derivative_chain: NameId,
    /// `CReal.hasDerivative_chain_id_sq : ∀ a b k1 k2, BoundedOn (fun _ =>
    /// one) a b k1 → BoundedOn (fun x => add x x) a b k2 →
    /// HasDerivativeOn (fun r => mul r r) (fun x => add x x) a b` — the
    /// chain rule's first concrete instantiation, `F := id`, `G := sq`.
    /// [`Self::has_derivative_chain`]'s own self-map hypotheses are
    /// `Equiv.refl`/hypothesis-projection trivial here (`id z` is defeq
    /// `z`), and [`Self::uniformly_continuous_id`] supplies the continuity
    /// hypothesis directly. The chain rule's raw output derivative is `fun x
    /// => mul (add x x) one`, not `fun x => add x x` — closed against
    /// [`Self::has_derivative_sq`]'s own stated derivative via
    /// [`Self::has_derivative_congr`] and [`Self::mul_one`]. `k1`/`k2` and
    /// their `BoundedOn` witnesses are left universally quantified (the
    /// `hasDerivative_cube` pattern) rather than derived, since deriving a
    /// concrete magnitude bound for `fun x => x+x` over an arbitrary `[a,b]`
    /// is a separate undertaking this instantiation does not need.
    pub has_derivative_chain_id_sq: NameId,

    // --- the integral (creal/integral.rs) -------------------------------------
    /// `CReal.riemannSum (f : CReal → CReal) (a b : CReal) (m : Nat) : CReal`
    /// — a left-endpoint Riemann sum over `[a, b]` with `Nat.succ m` equal
    /// subintervals: `sumRange (fun i => f(a + i·Δ)·Δ) (Nat.succ m)` with
    /// `Δ := (b − a) · ofRat (Rat.natDivSucc 1 m)`. See `integral.rs`'s
    /// module documentation for why the subinterval count is taken as
    /// `Nat.succ m` (so `Δ` needs no `CReal.inv`/`PosBound` witness) and why
    /// the sample point is the left endpoint.
    pub riemann_sum: NameId,
    /// `CReal.riemannSum_add : ∀ f g a b m,
    /// Equiv (riemannSum (fun r => add (f r) (g r)) a b m)
    ///       (add (riemannSum f a b m) (riemannSum g a b m))` — linearity in
    /// the integrand, the additive half.
    pub riemann_sum_add: NameId,
    /// `CReal.mul_riemannSum : ∀ c f a b m,
    /// Equiv (riemannSum (fun r => mul c (f r)) a b m) (mul c (riemannSum f a b m))`
    /// — linearity in the integrand, the scalar half.
    pub mul_riemann_sum: NameId,
    /// `CReal.riemannSum_le : ∀ f g a b m, le a b → (∀ z, le (f z) (g z)) →
    /// le (riemannSum f a b m) (riemannSum g a b m)` — monotonicity. The
    /// pointwise hypothesis is global (`∀ z`), not restricted to `[a, b]`;
    /// see `integral.rs`'s module documentation for why.
    pub riemann_sum_le: NameId,
    /// `CReal.riemannSum_const : ∀ c a b m,
    /// Equiv (riemannSum (fun _ => c) a b m) (mul c (add b (neg a)))` — a
    /// constant function's Riemann sum is exactly base times height,
    /// exactly (no error term), for every subinterval count `m`. See
    /// `integral.rs`'s module documentation for the two-piece route.
    pub riemann_sum_const: NameId,
    /// `CReal.ofNat_le : ∀ i j : Nat, Nat.le i j → CReal.le (ofNat i) (ofNat j)`
    /// — `CReal.ofNat` is monotone. Via `Nat.le_dest` (`∃ k, i + k = j`) plus
    /// `RatPrelude::nat_div_succ_le_add_left` (monotone in the numerator,
    /// stated additively so no `Nat`-subtraction appears) lifted across
    /// [`Self::of_rat_le`]; see `integral.rs`'s module documentation.
    pub of_nat_le: NameId,
    /// `CReal.riemannSum_sample_in_bounds : ∀ a b m i, le a b → Nat.lt i
    /// (Nat.succ m) → And (le a (add a (mul (ofNat i) delta))) (le (add a
    /// (mul (ofNat i) delta)) b)` — every LEFT-endpoint sample point of a
    /// Riemann sum over `[a, b]` lies in `[a, b]`; see `integral.rs`'s module
    /// documentation for the route.
    pub riemann_sample_in_bounds: NameId,
    /// `CReal.riemannSum_le_on : ∀ f g a b m, le a b → (∀ z, le a z → le z b →
    /// le (f z) (g z)) → le (riemannSum f a b m) (riemannSum g a b m)` —
    /// [`Self::riemann_sum_le`]'s pointwise hypothesis restricted to `[a, b]`,
    /// via [`Self::riemann_sample_in_bounds`]. See `integral.rs`'s module
    /// documentation; `riemann_sum_le` itself is UNCHANGED (both exist).
    pub riemann_sum_le_on: NameId,
    /// `CReal.sumRange_reblock : ∀ (g : Nat → CReal) (n k : Nat), Equiv
    /// (sumRange g (Nat.mul (Nat.succ n) k)) (sumRange (fun i => sumRange
    /// (fun j => g (Nat.add (Nat.mul (Nat.succ n) i) j)) (Nat.succ n)) k)`
    /// (`creal/integral.rs`) — regrouping `k · (n+1)` consecutive terms of an
    /// arbitrary `g` into `k` consecutive blocks of `n+1`, exactly, for an
    /// arbitrary (never-zero) block size. Generalizes the block-size-2
    /// special case (a dyadic-refinement reblocking, needed for the Chapter
    /// 13 integral's Cauchy-in-`m` estimate) from a fixed literal to an
    /// arbitrary `Nat.succ n`; see that file's own module documentation for
    /// the derivation and for what still separates this from
    /// `riemannSum_cauchy`.
    pub sum_range_reblock: NameId,
    /// `CReal.within_of_two_sided_le : ∀ t y : CReal, le t y → le (neg t) y →
    /// ∀ i : Nat, Within (seq t i) (add (seq y i) (natDivSucc 2 i))`
    /// (`creal/integral.rs`) — the general form of the "real inequality →
    /// `Within` at a chosen index" bridge `geometric.rs::geom_tail_within`
    /// builds bespoke for its own tail bound. See `integral.rs`'s own module
    /// documentation for the derivation and for why `geom_tail_within`
    /// could be re-derived from this without editing that file.
    pub within_of_two_sided_le: NameId,
    /// `CReal.le_add_of_abs_sub_le : ∀ x y : CReal, ∀ q : Rat, le (abs (add x
    /// (neg y))) (ofRat q) → le x (add y (ofRat q))` (`creal/integral.rs`) —
    /// roadmap step 2 toward `riemannSum_cauchy`: the abs-bound shape
    /// `UniformlyContinuousOn.spec`'s conclusion (and `fineSample_close`)
    /// produces splits into the CReal-level one-sided form `sumRange_le`
    /// consumes. Via `le_abs_self`, `le_trans`, `add_le_add`, and the
    /// add-rearrangement identity that folds `y + (x + (-y))` back to `x`.
    pub le_add_of_abs_sub_le: NameId,
    /// `CReal.two_sided_of_abs_sub_le : ∀ x y : CReal, ∀ q : Rat, le (abs
    /// (add x (neg y))) (ofRat q) → And (le x (add y (ofRat q))) (le y (add
    /// x (ofRat q)))` (`creal/integral.rs`) — the full abs-splitting lemma
    /// the per-block Riemann sum fold's two applications of `sumRange_le`
    /// (upper and lower) both need from a single `close_within` fact. The
    /// first conjunct reuses [`Self::le_add_of_abs_sub_le`] verbatim; the
    /// second mirrors its route with `neg_le_abs` in place of `le_abs_self`.
    pub two_sided_of_abs_sub_le: NameId,
    /// `CReal.fineBlockSum_close : ∀ F a b e m n i, le a b →
    /// UniformlyContinuousOn F a b → Nat.le i m → Nat.le deep m → And (le
    /// blockSum (add coarseTerm epsTerm)) (le coarseTerm (add blockSum
    /// epsTerm))` (`creal/integral.rs`) — roadmap step 3 toward
    /// `riemannSum_cauchy`: each coarse block's fine Riemann sub-sum bounded
    /// two-sidedly against the single coarse term `riemannSum` itself would
    /// use at that block, within `Δ_m · natDivSucc(1, e)`. Via
    /// `fineSample_close` per fine index, [`Self::two_sided_of_abs_sub_le`]
    /// to split it, and two applications of `sumRange_le` to lift the
    /// per-term bounds to the block sum.
    pub fine_block_sum_close: NameId,
    /// `CReal.hasDerivative_closeOfEquiv : ∀ F F' a b, HasDerivativeOn F F' a b →
    /// ∀ u v, le a u → le u b → le a v → le v b → Equiv u v → Equiv (F u) (F v)`
    /// — differentiability implies (local) continuity: two `Equiv`-related
    /// points inside the domain map to `Equiv`-related values. See
    /// `creal/monotone.rs`'s module documentation for why
    /// `monotone_of_nonneg_deriv` needs this (an interpolation endpoint built
    /// by dividing an interval into `K` equal pieces is only ever `Equiv` to
    /// the true endpoint, never syntactically equal to it).
    pub has_derivative_close_of_equiv: NameId,
    /// `CReal.expTerm : Nat → CReal := fun n => ofRat (Rat.normalize (Int.ofNat
    /// 1) (Nat.factorial n) (Nat.one_le_factorial n))` — the `n`-th term of the
    /// exponential series, `1/n!`, already reduced. See
    /// `creal/exponential.rs`'s module documentation.
    pub exp_term: NameId,
    /// `CReal.expSeriesPartial : Nat → CReal := CReal.sumRange CReal.expTerm`
    /// — the `k`-th partial sum `Σ_{n<k} 1/n!`. See `creal/exponential.rs`.
    pub exp_series_partial: NameId,
    /// `CReal.expTerm_le_geom : ∀ n, le (expTerm n) (ofRat (Rat.normalize 2
    /// (Nat.pow 2 n) _))` — `1/n! ≤ 2·(1/2)ⁿ` for every `n`, unconditional
    /// (no case split): both sides are `2` at `n=0` and `1` at `n=1`, and
    /// the ratio only widens from there. A pure `Rat`/`Nat` cross-
    /// multiplication proof (`creal/exponential.rs`), reducing to the `Nat`
    /// fact `2ⁿ ≤ 2·n!` — never touches `CReal.pow` or `CReal.inv`.
    pub exp_term_le_geom: NameId,
    /// `CReal.expDominant : Nat → CReal := fun n => mul two (pow half n)` —
    /// the `CReal.pow`-based reading of [`Self::exp_term_le_geom`]'s own
    /// bound `2·(1/2)ⁿ`, `half := ofRat (natDivSucc 1 1)`,
    /// `two := ofRat (normalize 2 1 _)`. See `creal/exponential.rs`.
    pub exp_dominant: NameId,
    /// `CReal.exp_term_le_dominant : ∀ n, le (expTerm n) (expDominant n)` —
    /// [`Self::exp_term_le_geom`], transported along `Rat.pow_natDivSucc_two`
    /// lifted through [`Self::of_rat_pow`] and rescaled by an explicit `2`,
    /// into the `CReal.pow`-based reading `expDominant` needs for
    /// [`Self::mul_sub_one_geom`]/[`Self::pow_half_le_nat_div_succ`]-style
    /// consumers. See `creal/exponential.rs::exp_dominant_equiv_r`.
    pub exp_term_le_dominant: NameId,
    /// `CReal.exp_term_nonneg : ∀ n, le zero (expTerm n)` — `1/n! ≥ 0`, by
    /// `rat_prelude/group.rs::zero_le_natDivSucc`'s own cross-multiplication
    /// technique, generalized off `natDivSucc`'s fixed denominator shape to
    /// the arbitrary positive denominator `Nat.factorial n`.
    pub exp_term_nonneg: NameId,
    /// `CReal.exp_dominant_nonneg : ∀ n, le zero (expDominant n)` — from
    /// [`Self::mul_nonneg`], `0 ≤ two`, and [`Self::pow_nonneg`] at
    /// `0 ≤ half`.
    pub exp_dominant_nonneg: NameId,
    /// `CReal.exp_term_abs_le_dominant : ∀ n, le (abs (expTerm n)) (expDominant n)`
    /// — [`Self::exp_term_le_dominant`] plus nonnegativity of both sides via
    /// [`Self::abs_le`], the exact domination shape
    /// [`Self::sum_range_cauchy_of_dominated`] and
    /// [`Self::sum_range_converges_of_dominated`] need.
    pub exp_term_abs_le_dominant: NameId,
    /// `CReal.sumRange_pow_half_closed_form : ∀ n, Equiv (sumRange (fun i =>
    /// pow half i) n) (mul two (add one (neg (pow half n))))` — the closed
    /// form of the base-`1/2` geometric partial sum, derived **without**
    /// `CReal.inv`/`PosBound`/`geometric.rs::geom_pair_within`: multiply
    /// [`Self::mul_sub_one_geom`]'s conclusion through by `two` and cancel
    /// `mul two (1 − half)` down to `one`. See `creal/exponential.rs`'s
    /// module documentation for the two new concrete `Rat` facts this needed
    /// (`2·(1/2)=1`, `1/2+1/2=1` — neither holds by `Eq.refl`; `Rat.normalize`
    /// does not unfold `Nat.gcd` by ι even for literal arguments) and why
    /// they were not needed for [`Self::exp_term_le_dominant`].
    pub sum_pow_half_closed_form: NameId,
    /// `CReal.cauchyOfPointwiseEquiv : ∀ G F, (∀ n, Equiv (G n) (F n)) →
    /// Cauchy G → Cauchy F` — the general lemma this lane built to scale a
    /// `Cauchy` witness across a pointwise `Equiv`, e.g. `CReal.mul_sumRange`'s
    /// index-shifted `mul c (sumRange f n) ~ sumRange (scaled f) n` bridge.
    /// See `creal/exponential.rs::declare_cauchy_of_pointwise_equiv`.
    pub cauchy_of_pointwise_equiv: NameId,
    /// `CReal.expDominantCauchy : Cauchy (sumRange expDominant)` — built via
    /// `CReal.converges_mul` (a constant sequence times the geometric partial
    /// sums, both convergent) plus [`Self::cauchy_of_pointwise_equiv`]
    /// transported across `CReal.mul_sumRange`'s `Equiv`, rather than
    /// re-deriving `CReal.mul`'s own index-shift bookkeeping by hand. See
    /// `creal/exponential.rs::declare_exp_dominant_cauchy`.
    pub exp_dominant_cauchy: NameId,
    /// `CReal.expSeriesPartialConverges : Exists CReal (fun L => Converges
    /// expSeriesPartial L)` — [`Self::sum_range_converges_of_dominated`]
    /// applied to [`Self::exp_term_abs_le_dominant`] and
    /// [`Self::exp_dominant_cauchy`]. See
    /// `creal/exponential.rs::declare_exp_series_partial_converges`.
    pub exp_series_partial_converges: NameId,
    /// `CReal.e := CReal.mk (speedup (diagonal expSeriesPartial) K) (…)` —
    /// Euler's number, built via `CReal.mk` on an EXPLICIT regular sequence
    /// (never an `Exists`-elimination into data): a concrete, non-existential
    /// `Cauchy` witness for `sumRange expDominant`
    /// (`exponential.rs::exp_dominant_cauchy_body_concrete`, redone by hand
    /// through `CReal.mul`'s own index shift, since
    /// [`Self::exp_dominant_cauchy`]'s existential form cannot supply `K` as
    /// data) feeds `CReal.sumRange_cauchy_dominated_ordered_normalized` and
    /// `CReal.regular_of_scaled_cauchy`. See
    /// `creal/exponential.rs::declare_e`.
    pub e: NameId,
    /// `CReal.e_converges : Converges expSeriesPartial e` — `e`'s own
    /// defining property, and the missing link every OTHER property of `e`
    /// (`two_le_e`, `e_le_four`, …) is built on. See
    /// `creal/exponential.rs::declare_e_converges`.
    pub e_converges: NameId,
    /// `CReal.two_le_e : le two e` — the first NUMERIC bound on Euler's
    /// number. Needs an EVENTUAL argument
    /// ([`Self::converges_lower_bound_shift`]), not
    /// [`Self::converges_lower_bound`] directly: `expSeriesPartial 0 = 0 <
    /// 2`, so the bound only holds from index `2` on, where monotonicity
    /// (`CReal.sumRange_mono_outer` at the nonnegative summand `expTerm`)
    /// takes over. See `creal/exponential.rs::declare_two_le_e`.
    pub two_le_e: NameId,
    /// `CReal.e_le_four : le e four` — an upper bound on Euler's number, from
    /// the SAME domination `expTerm n ≤ expDominant n` this file already
    /// built for the Cauchy argument, summed via `CReal.sumRange_le` and the
    /// closed form `CReal.sumRange_pow_half_closed_form`: `Σ expDominant n =
    /// 2·Σ(1/2)ⁱ = 2·(2·(1−(1/2)ⁿ)) ≤ 4`. No shift needed — this bound holds
    /// at every `n`, including `n = 0`, unlike [`Self::two_le_e`]. See
    /// `creal/exponential.rs::declare_e_le_four` for why `4`, not the
    /// classically sharper `3`: the bound as built doubles a bound that is
    /// already loose by a factor of `2·(1/2)⁰ = 2` at `n = 0`/`1`, and
    /// tightening it needs an index-`2` split this slice does not attempt.
    pub e_le_four: NameId,
    /// `CReal.e_le_three : le e three`, `three := add two one` — the classical
    /// index-2 split sharpening [`Self::e_le_four`]: `e = Σ 1/n! = 1 + 1 +
    /// Σ_{n≥2} 1/n!`, the first two terms exact, and for `n ≥ 2`, `1/n! ≤
    /// (1/2)^(n-1)` so the tail is at most `Σ_{k≥1} (1/2)^k = 1`. Built
    /// WITHOUT any new `Nat`-level factorial fact: the shifted pointwise bound
    /// `expTerm (k+2) ≤ pow half (k+1)` is [`Self::exp_term_le_dominant`] at
    /// `k+2` composed with the pure `CReal`-algebra identity `2 · pow half
    /// (succ m) ~ pow half m` (`pow_succ`'s ι-unfold + `mul_assoc` +
    /// `mul_comm` + `2·half ~ 1`), and the tail sum is closed by an induction
    /// proving `∀ k, sumRange expTerm (k+2) + pow half k ≤ three` (the
    /// telescoping invariant, tight at `k = 0`: `2 + 1 = 3`), then the same
    /// shifted identity in its ADDITIVE form (`pow half (k+1) + pow half
    /// (k+1) ~ pow half k`, via `left_distrib` + `half + half ~ 1`) closes the
    /// step. The top-level statement over ALL `n` (not just `n ≥ 2`) needs a
    /// genuine case split — `expTerm 0 = expTerm 1 = 1`, not yet geometric —
    /// so unlike [`Self::e_le_four`] this is NOT one uniform `∀n` bound but a
    /// nested `Nat.rec` on `{0, 1, k+2}`, matching the mathematical kink at
    /// index `2` rather than an artifact of the formalization. See
    /// `creal/exponential.rs::declare_e_le_three`.
    pub e_le_three: NameId,
    /// `CReal.cosTerm : Nat → CReal := fun k => mul (pow (neg one) k)
    /// (expTerm (Nat.add k k))` — the `k`-th term of `cos 1`'s Taylor series,
    /// `(-1)^k/(2k)!`, the doubled index written `Nat.add k k` (not `Nat.mul
    /// 2 k`) so `CReal.pow_add` applies to it with no reduction bookkeeping.
    /// See `creal/trig.rs`.
    pub cos_term: NameId,
    /// `CReal.cosSeriesPartial : Nat → CReal := CReal.sumRange CReal.cosTerm`
    /// — the `k`-th partial sum `Σ_{n<k} (-1)^n/(2n)!`. See `creal/trig.rs`.
    pub cos_series_partial: NameId,
    /// `CReal.cosTermAbsLeDominant : ∀ k, le (abs (cosTerm k)) (expDominant
    /// k)` — the domination bound closing `Cauchy (sumRange cosTerm)` against
    /// `CReal.e`'s own `expDominant`/`expDominantCauchy` machinery, reused
    /// unchanged rather than re-derived: no new geometric series. From a
    /// sign bound (`abs (pow (neg one) k) ≤ one`, by induction, no parity
    /// case split) and `CReal.exp_term_abs_le_dominant` (already built for
    /// `e`) composed via `CReal.abs_mul_le_of_bounds`, plus a small
    /// monotonicity argument (`expDominant (Nat.add k k) ≤ expDominant k`,
    /// since `pow half` squares into `[0,1]`). See `creal/trig.rs`.
    pub cos_term_abs_le_dominant: NameId,
    /// `CReal.cosOne := CReal.mk (speedup (diagonal cosSeriesPartial) K) (…)`
    /// — `cos 1`, the first transcendental-function-family constant in this
    /// kernel, built via `CReal.mk` on an explicit regular sequence exactly
    /// as `CReal.e` is (never by `Exists`-elimination). `K` and its concrete
    /// Cauchy-body proof come from reproducing
    /// `exponential.rs::exp_dominant_cauchy_body_concrete` (the SAME value
    /// `CReal.e`'s own construction uses, since `cosOne`'s domination series
    /// **is** `expDominant`, not a new one) — see `creal/trig.rs`'s module
    /// documentation for why that reproduction, rather than an edit to that
    /// file, is the route taken. Neither `CReal.cosOneConverges` (the
    /// analogue of `CReal.e_converges`) nor a `[0, 1]` bound are built here.
    pub cos_one: NameId,
    /// `CReal.cosOneConverges : Converges cosSeriesPartial cosOne` -- the
    /// `e_converges` analogue, built the same way: generically over a BOUND
    /// `(k, h)` (mirroring `declare_converges_of_cauchy`'s own `minor`
    /// closure, never over the CONCRETE `k_final` -- see
    /// `exponential.rs::declare_e_converges`'s own module note on why the
    /// concrete form overflows a 1 GiB release stack), substituting the
    /// concrete `(k_final, cosSeriesPartialBody)` only in the final
    /// Pi-application. See `creal/trig.rs`.
    pub cos_one_converges: NameId,
    /// `CReal.cosOne_le_four : le cosOne (mul two two)` -- a LOOSE, UNIFORM
    /// bound (no case split, holds at every `n` including `n = 0`), the same
    /// shape as `CReal.e_le_four`: `abs (cosSeriesPartial n) <= sumRange
    /// expDominant n <= four`, via `CReal.abs_sumRange_le` (the triangle
    /// inequality) composed with `CReal.sumRange_le` at the pointwise
    /// `CReal.cosTermAbsLeDominant`, then the SAME closed-form geometric
    /// bound `e_le_four` derives for `sumRange expDominant n`. Deliberately
    /// not the sharper `[0, 1]`/`[1/2, 3/5]` a genuine alternating-series
    /// argument would give (that needs pairing consecutive terms, which is
    /// real new machinery this slice does not build) -- see
    /// `creal/trig.rs`'s module documentation for the tradeoff.
    pub cos_one_le_four: NameId,
    /// `CReal.neg_four_le_cosOne : le (neg (mul two two)) cosOne` -- the
    /// lower half of [`Self::cos_one_le_four`]'s bound, by the same `abs
    /// (cosSeriesPartial n) <= four` per-`n` fact read through
    /// `neg_le_abs`/`neg_le_neg`/double-negation instead of `le_abs_self`.
    pub neg_four_le_cos_one: NameId,
    /// `CReal.expTerm_antitone : ∀ n, le (expTerm (succ n)) (expTerm n)` --
    /// `1/(n+1)! <= 1/n!`, a pure `Rat`/`Nat` cross-multiplication fact about
    /// `CReal.expTerm` (never touching `CReal.inv`, since `expTerm n :=
    /// ofRat (1/n!)` is already a raw normalized rational). Declared from
    /// `creal/trig.rs` (after `exponential::declare_e_family`, per
    /// `creal.rs`'s own ordering) rather than `creal/exponential.rs` itself,
    /// which another lane owns. This is the `hdec` premise
    /// `CReal.alternatingLowerBound`/`upperBound` need at `cosTerm`'s
    /// magnitude sequence -- see `creal/trig.rs`.
    pub exp_term_antitone: NameId,
    /// `CReal.cosOne_alternating_lower : ∀ m, le (sumRange cosTerm (add m m))
    /// cosOne` -- [`Self::alternating_lower_bound`] instantiated at
    /// `cosTerm`'s magnitude sequence `a j := expTerm (add j j)`, closing
    /// `hnn` from `CReal.exp_term_nonneg` and `hdec` from
    /// [`Self::exp_term_antitone`] (doubled via `Nat.succ_add`), against the
    /// limit hypothesis `CReal.cosOneConverges`. See `creal/trig.rs`.
    pub cos_one_alternating_lower: NameId,
    /// `CReal.cosOne_alternating_upper : ∀ m, le cosOne (sumRange cosTerm
    /// (succ (add m m)))` -- the mirror of
    /// [`Self::cos_one_alternating_lower`], off
    /// [`Self::alternating_upper_bound`]. See `creal/trig.rs`.
    pub cos_one_alternating_upper: NameId,
    /// `CReal.cosOne_nonneg : le zero cosOne` --
    /// [`Self::cos_one_alternating_lower`] at `m := 0`: `sumRange cosTerm
    /// (add 0 0)` is ι-defeq to `zero`, so the general bracket specializes
    /// to the sign bound for free -- the first concrete numeric fact this
    /// development has about `cosOne` (previously only `[-4, 4]`, which does
    /// not even pin the sign). See `creal/trig.rs`.
    pub cos_one_nonneg: NameId,
    /// `CReal.cosOne_le_exp_term_zero : le cosOne (expTerm 0)` --
    /// [`Self::cos_one_alternating_upper`] at `m := 0`, folded through
    /// `add_comm`/`add_zero`/`one_mul` via `le_congr`. `expTerm 0` is
    /// mathematically `1` (`1/0! = 1`) but is not reduced to the literal
    /// `CReal.one` here -- that needs `Rat.normalize 1 (factorial 0) _ =
    /// Rat.one`, i.e. `Nat.gcd 1 1` computing to `1`, which does not hold by
    /// `Eq.refl` and was out of scope for this slice. See `creal/trig.rs`.
    pub cos_one_le_exp_term_zero: NameId,
    /// `CReal.negOnePowDouble : ∀ k, Equiv (pow (neg one) (add k k)) one` --
    /// `(-1)^(2k) = 1` for every `k`, by plain induction on `k` (no parity
    /// case split). `creal/alternating.rs`'s parity fact underneath the
    /// Leibniz (alternating series) pairing argument.
    pub neg_one_pow_double: NameId,
    /// `CReal.alternatingELeO : ∀ a, (∀ k, le zero (a k)) → ∀ k, le
    /// (sumRange t (add k k)) (sumRange t (succ (add k k)))`, where `t j :=
    /// mul (pow (neg one) j) (a j)` -- the same-index half of
    /// `creal/alternating.rs`'s Leibniz pairing argument: an even-count
    /// partial sum never exceeds the odd-count partial sum one term past it.
    pub alternating_e_le_o: NameId,
    /// `CReal.alternatingBracket : ∀ a, (∀ k, le zero (a k)) → (∀ k, le (a
    /// (succ k)) (a k)) → ∀ m i, And (le (E m) (E (add m i))) (le (E m) (O
    /// (add m i)))`, `E x := sumRange t (add x x)`, `O x := sumRange t (succ
    /// (add x x))`, `t j := mul (pow (neg one) j) (a j)` -- the Leibniz
    /// (alternating series) criterion's pairing argument: from `m` onward,
    /// every even-count partial sum climbs monotonically and stays below
    /// every odd-count partial sum. `creal/alternating.rs`'s module
    /// documentation explains why closing this to an actual limit bound (and
    /// hence a concrete numeric bound on `cosOne`) is a sized, separately
    /// tractable next step this declaration does not itself reach.
    pub alternating_bracket: NameId,
    /// `CReal.alternatingBracketUpper : ∀ a, (∀ k, le zero (a k)) → (∀ k, le
    /// (a (succ k)) (a k)) → ∀ m i, And (le (E (add m i)) (O m)) (le (O (add
    /// m i)) (O m))` -- the DUAL of [`Self::alternating_bracket`]: from `m`
    /// onward, every even-count AND every odd-count partial sum sits at or
    /// below `O m`. Same induction shape, using `O`'s own one-step decrease
    /// (`creal/alternating.rs`'s private `o_step_le`) in place of `E`'s
    /// one-step increase. Needed because this development has no
    /// `converges_upper_bound_shift`: closing `L ≤ O m` routes through
    /// [`Self::converges_lower_bound_shift`] on the NEGATED sequence, which
    /// needs this dual bracket's per-index upper bound, not
    /// `alternating_bracket`'s lower one. See `creal/alternating.rs`.
    pub alternating_bracket_upper: NameId,
    /// `CReal.alternatingLowerBound : ∀ a, (∀ k, le zero (a k)) → (∀ k, le (a
    /// (succ k)) (a k)) → ∀ L, Converges (sumRange t) L → ∀ m, le (E m) L`,
    /// `t`/`E` as in [`Self::alternating_bracket`] -- the bracket CLOSED
    /// against the actual limit, using `Nat.even_or_odd`'s computed parity
    /// split to bridge an arbitrary shift `n` to `alternating_bracket`'s
    /// paired-index conclusion (`n = k+k` lands on the `E` side, `n =
    /// succ(k+k)` on the `O` side), then
    /// [`Self::converges_lower_bound_shift`] at shift `s := add m m`. See
    /// `creal/alternating.rs`.
    pub alternating_lower_bound: NameId,
    /// `CReal.alternatingUpperBound : ∀ a, (∀ k, le zero (a k)) → (∀ k, le (a
    /// (succ k)) (a k)) → ∀ L, Converges (sumRange t) L → ∀ m, le L (O m)` --
    /// the mirror of [`Self::alternating_lower_bound`], via
    /// [`Self::converges_neg`]/[`Self::neg_le_neg`] rather than a second
    /// shift-bound direction (this development has no
    /// `converges_upper_bound_shift`). See `creal/alternating.rs`.
    pub alternating_upper_bound: NameId,
    /// `CReal.sumRange_const : ∀ w m,
    /// Equiv (sumRange (fun _ => w) (Nat.succ m)) (mul (ofNat (Nat.succ m))
    /// w)` (`creal/monotone.rs`) — a constant summed `succ m` times is
    /// exactly `(succ m)` copies of it, piece count left symbolic. Generalizes
    /// `integral.rs`'s private `riemann_sum_const_core` (which only ever
    /// multiplies by a fixed `ofNat n` already produced by that file's own
    /// `mesh_inverse_identity`) into a standalone, reusable fact:
    /// `monotone_of_nonneg_deriv` needs it to fold a telescoped subdivision
    /// sum down to a single product before the Archimedean closing step.
    pub sum_range_const: NameId,
    /// `CReal.mesh_count_width : ∀ width m,
    /// Equiv (mul (ofNat (Nat.succ m)) (mul width (ofRat (natDivSucc 1
    /// m)))) width` (`creal/monotone.rs`) — dividing an interval of length
    /// `width` into `succ m` equal pieces and multiplying back by the piece
    /// count recovers `width` exactly, for every `m`. Generalizes
    /// `integral.rs`'s private `mesh_times_count_eq_width` (already general
    /// in `width`, not tied to that file's own Riemann-sum `a`/`b`) into a
    /// standalone, reusable fact.
    pub mesh_count_width: NameId,
    /// `CReal.subdivisionPoint_in_bounds : ∀ a b m i, le a b → Nat.le i
    /// (Nat.succ m) → And (le a (add a (mul (ofNat i) step))) (le (add a
    /// (mul (ofNat i) step)) b)`, `step := mul (add b (neg a)) (ofRat
    /// (natDivSucc 1 m))` (`creal/monotone.rs`) — a trivial generalization of
    /// `integral.rs`'s `riemannSum_sample_in_bounds` from `Nat.lt` to
    /// `Nat.le`, so it also reaches the LAST subdivision point (`i = Nat.succ
    /// m`), which that theorem does not: its own hypothesis is already
    /// `Nat.le`-shaped internally, so no `Nat.lt → Nat.le` conversion is
    /// needed here at all.
    pub subdivision_point_in_bounds: NameId,
    /// `CReal.sumRange_double : ∀ (g : Nat → CReal) (k : Nat), Equiv
    /// (sumRange g (Nat.mul 2 k)) (sumRange (fun i => add (g (Nat.mul 2 i))
    /// (g (Nat.succ (Nat.mul 2 i)))) k)` (`creal/integral.rs`) — grouping
    /// `2k` consecutive terms of an arbitrary `g` into `k` consecutive
    /// pairs, exactly (no error term). The reblocking identity a
    /// dyadic-refinement comparison of `riemannSum` at subdivision counts
    /// `m` and `2m+1` needs; see `integral.rs`'s module documentation for
    /// what still separates this from `riemannSum_cauchy`.
    pub sum_range_double: NameId,
    /// `CReal.ofNat_add : ∀ a b : Nat, Equiv (ofNat (Nat.add a b)) (add (ofNat
    /// a) (ofNat b))` (`creal/integral.rs`) — `CReal.ofNat` is a `Nat →
    /// (CReal, +)` homomorphism. Direct, non-inductive: `ofNat a := ofRat
    /// (natDivSucc a 0)`, so [`Self::of_rat_add`] gives `Equiv (add (ofNat a)
    /// (ofNat b)) (ofRat (Rat.add (natDivSucc a 0) (natDivSucc b 0)))`, and
    /// `RatPrelude::nat_div_succ_add` at denominator index `0` collapses the
    /// right side's `Rat.add` to the single `natDivSucc (Nat.add a b) 0` —
    /// defeq `ofNat (Nat.add a b)` — with no induction on either argument.
    /// Needed to reconcile [`Self::sum_range_reblock`]'s raw global fine
    /// index `(succ n)·i + j` with the per-block local sample-point
    /// arithmetic `riemannSum_cauchy` still needs; see `integral.rs`'s
    /// module documentation.
    pub of_nat_add: NameId,
    /// `CReal.ofNat_mul : ∀ a b : Nat, Equiv (ofNat (Nat.mul a b)) (mul (ofNat
    /// a) (ofNat b))` (`creal/integral.rs`) — `CReal.ofNat` is also a `Nat →
    /// (CReal, ·)` homomorphism, by the same direct route as
    /// [`Self::of_nat_add`]: [`Self::of_rat_mul`] plus
    /// `RatPrelude::nat_div_succ_mul` (`Rat.mul (natDivSucc a 0) (natDivSucc
    /// b j) = natDivSucc (a·b) j`, already stated for an arbitrary second
    /// denominator index `j`, so `j := 0` is exactly this case) — no
    /// induction.
    pub of_nat_mul: NameId,
    /// `CReal.monotone_of_nonneg_deriv : ∀ F F' a b, HasDerivativeOn F F' a
    /// b → (∀ z, le a z → le z b → le zero (F' z)) → ∀ x y, le a x → le x y →
    /// le y b → le (F x) (F y)` (`creal/monotone.rs`) — a nonnegative
    /// derivative on `[a, b]` makes `F` monotone there. See that module's
    /// documentation for the subdivision construction and why
    /// [`Self::has_derivative_close_of_equiv`] is needed at BOTH
    /// interpolation endpoints, not only the last one the original two-lane
    /// handoff plan named.
    pub monotone_of_nonneg_deriv: NameId,

    /// `CReal.strict_mono_of_pos_deriv : ∀ F F' a b, HasDerivativeOn F F' a b
    /// → ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
    /// ∀ x y, le a x → lt x y → le y b → lt (F x) (F y)` (`creal/monotone.rs`)
    /// — the STRICT companion of [`Self::monotone_of_nonneg_deriv`]: a
    /// derivative *uniformly bounded away from zero* by `1/(k+1)` on `[a,b]`
    /// makes `F` strictly increasing there, given a strict input gap
    /// (`lt x y`, not merely `le x y` — the conclusion is false at a
    /// degenerate `x ~ y`, so this is genuinely required, not a convenience).
    ///
    /// The hypothesis is a `Nat`-indexed UNIFORM bound (`PosBound (F' z) k`'s
    /// own shape, spelled out rather than named) rather than the pointwise
    /// `∀ z, lt zero (F' z)`: the pointwise form hands a *different* rational
    /// witness at every `z`, and nothing in this development extracts one
    /// witness usable across an entire subdivision from that (no compactness
    /// argument exists here, deliberately — see the module documentation for
    /// why this is the honest choice, not a weakening).
    ///
    /// Built by halving the given bound (`CReal.strict_mono_of_pos_deriv`'s
    /// own module doc: `Rat.natDivSucc_halve` + `Rat.natDivSucc_add` fuse
    /// `1/(2k+2) + 1/(2k+2) = 1/(k+1)`) to get an error tolerance strictly
    /// below the derivative's own lower bound, subdividing finely enough
    /// (exactly [`Self::monotone_of_nonneg_deriv`]'s own construction) that
    /// `hd_spec`'s error term stays under that tolerance on every piece, and
    /// telescoping the resulting **positive** per-piece lower bound
    /// `(1/(2k+2))·step` up to `(1/(2k+2))·(y−x)` — a REAL, not yet rational,
    /// lower bound on `F y − F x`. The strict input gap `lt x y` supplies a
    /// rational `r > 0` with `embed r ≤ y−x`; multiplying it by the rational
    /// `1/(2k+2)` (via `CReal.ofRat_mul`, a genuine `Rat` product, not a
    /// `CReal` one) produces the RATIONAL gap `CReal.lt` demands.
    pub strict_mono_of_pos_deriv: NameId,

    /// `CReal.strict_mono_magnitude : ∀ F F' a b, HasDerivativeOn F F' a b →
    /// ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
    /// ∀ x y, le a x → le x y → le y b →
    /// le (mul (ofRat (natDivSucc 1 (2·k+2))) (add y (neg x)))
    ///    (add (F y) (neg (F x)))` (`creal/monotone.rs`) — the RATE
    /// [`Self::strict_mono_of_pos_deriv`] proves internally (as `chained2` in
    /// that function's own derivation) but never used to declare: `F y − F x`
    /// is bounded BELOW by the derivative floor `1/(2(k+1))` times the input
    /// gap, not merely shown positive. Takes `le x y`, not `lt x y` — nothing
    /// in the subdivision argument up to this exact inequality needs a
    /// strict gap (it degenerates correctly to `0 ≤ 0` at `x = y`); strictness
    /// is only needed downstream to turn a REAL lower bound into a RATIONAL
    /// `CReal.lt` witness, which is exactly what
    /// [`Self::strict_mono_of_pos_deriv`] does on top of this lemma.
    ///
    /// [`Self::strict_mono_of_pos_deriv`] now calls this lemma directly for
    /// that inequality rather than re-deriving it: the whole subdivision /
    /// telescope construction (the piece count, the per-piece bound, the
    /// telescope, the algebraic regrouping to `(1/(2(k+1)))·(y−x)`) lives here
    /// exactly once. Two consumers outside `monotone.rs` are blocked on
    /// reaching it: an exact IVT root (`|x−y| ≤ 2(k+1)·(|F x|+|F y|)` follows
    /// directly) and Chapter 12's inverse-function continuity (a lower bound
    /// on `F`'s growth is an upper bound on `F⁻¹`'s modulus).
    pub strict_mono_magnitude: NameId,

    /// `CReal.scale_cancel_le : ∀ (m : Nat) (u v : CReal),
    /// le (mul (ofRat (natDivSucc 1 m)) u) v → le u (mul (ofNat (Nat.succ m)) v)`
    /// (`creal/monotone.rs`) — the rational-cancellation step two lanes
    /// independently stopped on: [`Self::strict_mono_magnitude`] (and every
    /// other place this development samples at the recurring `1/(m+1)`
    /// shape) produces a bound `(1/(m+1))·u ≤ v`, and turning that into a
    /// bound on `u` alone means multiplying through by `(m+1)` and
    /// cancelling `(m+1)·(1/(m+1)) = 1`. Stated at a bare `m`, not at
    /// [`Self::strict_mono_magnitude`]'s own instantiation `m := 2k+1`,
    /// because `Rat.natDivSucc 1 m` is the single recurring "epsilon" this
    /// whole file samples at — narrowing the shape to one call site would
    /// just mean rebuilding it at the next.
    pub scale_cancel_le: NameId,

    /// `CReal.diff_le_of_strict_mono_magnitude : ∀ F F' a b,
    /// HasDerivativeOn F F' a b → ∀ k, (∀ z, le a z → le z b →
    /// le (ofRat (natDivSucc 1 k)) (F' z)) → ∀ x y, le a x → le x y → le y b
    /// → le (add y (neg x)) (mul (ofNat (Nat.succ (Nat.succ (Nat.mul 2 k))))
    /// (add (abs (F x)) (abs (F y))))` (`creal/monotone.rs`) —
    /// [`Self::strict_mono_magnitude`] cancelled by [`Self::scale_cancel_le`]
    /// against the triangle inequality: a LOWER bound on `F`'s growth
    /// becomes an UPPER bound on how far apart `x` and `y` can be for a
    /// given spread of `F` values, `|x−y| ≤ 2(k+1)·(|Fx|+|Fy|)` — the exact
    /// IVT root and Chapter 12's inverse-function continuity both need this
    /// direction. Left as `add y (neg x)` rather than wrapped in `CReal.abs`:
    /// the hypotheses already give `x ≤ y`, so this term IS the (nonnegative)
    /// difference, and no public `CReal.abs_of_nonneg`-shaped fact exists yet
    /// to fold that in for free.
    pub diff_le_of_strict_mono_magnitude: NameId,

    /// `CReal.strict_injective_of_pos_deriv : ∀ F F' a b, HasDerivativeOn F
    /// F' a b → ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k))
    /// (F' z)) → ∀ x y, le a x → le x b → le a y → le y b → Apart x y →
    /// Apart (F x) (F y)` (`creal/monotone.rs`) — Spivak ch. 12's entry point
    /// for inverse functions: a uniformly positive derivative on `[a,b]`
    /// makes `F` injective there, in the constructive (apartness) sense.
    /// `Or.elim` on `Apart x y := lt x y ∨ lt y x` applies
    /// [`Self::strict_mono_of_pos_deriv`] to whichever ordered pair the
    /// witness supplies — never deciding which, since the witness already
    /// says so.
    pub strict_injective_of_pos_deriv: NameId,

    /// `creal/inverse_fn.rs`'s own 2 names, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.inverse_fn.order_reflect_of_pos_deriv` and documented in
    /// [`InverseFnNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub inverse_fn: InverseFnNames,

    /// `CReal.inverse_lipschitz_of_pos_deriv : ∀ F F' a b, HasDerivativeOn F
    /// F' a b → ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k))
    /// (F' z)) → ∀ x y, le a x → le x b → le a y → le y b → Apart x y →
    /// le (abs (add x (neg y))) (mul (ofNat (Nat.succ e_acc))
    /// (abs (add (F x) (neg (F y)))))`, `e_acc := Nat.succ (Nat.mul 2 k)`
    /// (`creal/monotone.rs`) — Chapter 12's CONTINUITY-of-the-inverse
    /// statement: a two-sided Lipschitz bound on the DOMAIN gap in terms of
    /// the CODOMAIN gap, so a caller who already has `F x` close to `F y`
    /// (plus `Apart x y` as data) gets `x` close to `y`, without ever
    /// deciding the order of `x`/`y` from the codomain fact alone the way
    /// unconditional order-reflection would need.
    ///
    /// Composes two already-proved pieces, one per branch of the case split
    /// on the given `Apart x y`: [`Self::strict_mono_magnitude`] gives the
    /// RAW bound `(1/(2k+2))·(hi−lo) ≤ F hi − F lo` for whichever of
    /// `x`/`y` is smaller, and [`Self::scale_cancel_le`] clears the
    /// fraction to `(hi−lo) ≤ (2k+2)·(F hi − F lo)`. Turning that
    /// ONE-sided, order-dependent bound into the two-sided `abs` statement
    /// needs [`Self::abs_le`] plus a small ring identity this file builds
    /// locally (`neg (add x (neg y))` `Equiv` `add y (neg x)`, i.e.
    /// `neg (x−y) ~ (y−x)` — the same distributivity fact `creal/series.rs`
    /// and `creal/derivative.rs` each already carry their own private copy
    /// of, as `neg_add`/`neg_add_distrib`) to identify `neg (x−y)` with
    /// `y−x` and transport the one-sided bound across it, plus
    /// [`Self::mul_le_mul_of_nonneg_left`] to widen `F hi − F lo` to
    /// `abs (F x − F y)` (needing `0 ≤ (2k+2)`, from [`Self::of_nat_le`]
    /// against `Nat.zero_le`) and [`Self::add_le_add`]/[`Self::add_neg`] for
    /// the sign facts (`x−y ≤ 0 ≤ (2k+2)·(F hi−F lo)` in the branch where
    /// `x < y`, and its mirror).
    ///
    /// Unlike [`InverseFnNames::order_reflect_of_pos_deriv`], this does NOT need the
    /// codomain hypothesis `lt (F x) (F y)` at all — it bounds the gap in
    /// BOTH directions from `Apart x y` alone, which is what makes it a
    /// genuine continuity-of-the-inverse statement rather than a restatement
    /// of order-reflection.
    pub inverse_lipschitz_of_pos_deriv: NameId,

    /// `CReal.ivt_step : ∀ F P Q eps, lt zero eps → le P Q → le (F P) eps →
    /// le (neg eps) (F Q) → ∃ P' Q', le P P' ∧ le P' Q' ∧ le Q' Q ∧
    /// le (F P') eps ∧ le (neg eps) (F Q') ∧ Equiv (add Q' (neg P')) (mul
    /// (add Q (neg P)) (ofRat (natDivSucc 1 1)))` (`creal/ivt.rs`) — the one
    /// bisection step of the constructive approximate Intermediate Value
    /// Theorem: bisect `[P, Q]` at its midpoint `m`, decide via
    /// [`Self::lt_cotrans`] applied to the fixed strict pair `neg eps < eps`
    /// at `F m` (never at the undecidable exact sign of `F m` itself), and
    /// land in whichever half keeps the sign invariant, at exactly half the
    /// width. See that module's documentation for the full paper argument.
    pub ivt_step: NameId,
    /// `CReal.constant_of_zero_deriv : ∀ F F' a b, HasDerivativeOn F F' a b →
    /// (∀ z, le a z → le z b → Equiv (F' z) zero) → ∀ x y, le a x → le x y →
    /// le y b → Equiv (F x) (F y)` (`creal/monotone.rs`) — a vanishing
    /// derivative on `[a, b]` makes `F` constant there (Spivak ch. 11).
    /// Applies [`Self::monotone_of_nonneg_deriv`] TWICE — once to `F`
    /// directly, once to `neg ∘ F` via [`Self::has_derivative_neg`] — and
    /// closes the resulting `le (F x) (F y)`/`le (F y) (F x)` pair with
    /// `equiv_of_le_le`. No Mean Value Theorem, no case split on `CReal.le`.
    pub constant_of_zero_deriv: NameId,
    /// `CReal.antitone_of_nonpos_deriv : ∀ F F' a b, HasDerivativeOn F F' a
    /// b → (∀ z, le a z → le z b → le (F' z) zero) → ∀ x y, le a x → le x y
    /// → le y b → le (F y) (F x)` (`creal/monotone.rs`) — the mirror of
    /// [`Self::monotone_of_nonneg_deriv`]: a nonpositive derivative on
    /// `[a, b]` makes `F` antitone there, via the same `neg ∘ F` trick
    /// [`Self::constant_of_zero_deriv`] uses for its second direction.
    pub antitone_of_nonpos_deriv: NameId,
    /// `CReal.strict_antitone_of_neg_deriv : ∀ F F' a b, HasDerivativeOn F F'
    /// a b → ∀ k, (∀ z, le a z → le z b → le (F' z) (neg (ofRat (natDivSucc 1
    /// k)))) → ∀ x y, le a x → lt x y → le y b → lt (F y) (F x)`
    /// (`creal/monotone.rs`) — the STRICT mirror of
    /// [`Self::antitone_of_nonpos_deriv`], built the same way that theorem
    /// was built from [`Self::monotone_of_nonneg_deriv`]: apply
    /// [`Self::strict_mono_of_pos_deriv`] to `neg ∘ F` via
    /// [`Self::has_derivative_neg`], against a uniformly-negative derivative
    /// bounded away from zero by `1/(k+1)`, then flip the resulting
    /// `lt (neg (F x)) (neg (F y))` back to `lt (F y) (F x)` via a
    /// generic `lt (neg u) (neg v) → lt v u` derived from the field axioms
    /// (this development has `neg_le_neg` for `le` but no strict analogue).
    pub strict_antitone_of_neg_deriv: NameId,
    /// `CReal.strict_mono_comp : ∀ F G a b c d, (∀ x y, le a x → lt x y → le
    /// y b → lt (F x) (F y)) → (∀ x y, le c x → lt x y → le y d → lt (G x)
    /// (G y)) → (∀ z, le a z → le z b → le c (F z)) → (∀ z, le a z → le z b →
    /// le (F z) d) → ∀ x y, le a x → lt x y → le y b → lt (G (F x)) (G (F y))`
    /// (`creal/monotone.rs`) — Spivak ch. 12's composition corollary: a
    /// strictly increasing `F` composed with a strictly increasing `G` is
    /// strictly increasing. Stated over the strict-monotonicity
    /// CONCLUSIONS directly (not `HasDerivativeOn`/`hasDerivative_neg`'s
    /// chain rule, whose shared-interval self-map hypothesis would force `G`
    /// onto `F`'s own domain rather than `F`'s range) plus an explicit range
    /// hypothesis (`F` maps `[a, b]` into `[c, d]`); composing the two `lt`
    /// facts is then direct function application.
    pub strict_mono_comp: NameId,

    /// `CReal.ivt_iter : ∀ F P0 Q0 eps, lt zero eps → le P0 Q0 → le (F P0)
    /// eps → le (neg eps) (F Q0) → ∀ n : Nat, ∃ P Q, le P0 P ∧ le P Q ∧ le Q
    /// Q0 ∧ le (F P) eps ∧ le (neg eps) (F Q) ∧ Equiv (add Q (neg P)) (mul
    /// (add Q0 (neg P0)) (pow (ofRat (natDivSucc 1 1)) n))` (`creal/ivt.rs`)
    /// -- [`Self::ivt_step`] iterated `n` times by structural `Nat`
    /// induction, carrying the six-part invariant with the ORIGINAL
    /// endpoints `P0, Q0` fixed throughout (`ivt_step`'s own `cp`/`cq` slots
    /// are always the CURRENT bracket, one level in). The width at step `n`
    /// is `(Q0 - P0) * (1/2)^n`, tracked via [`Self::pow`] and never via an
    /// explicit `pow_succ`/`pow_zero` lemma application: `pow`'s own
    /// `Nat.rec` ι-reduces `pow half (succ j)` to `mul (pow half j) half`
    /// definitionally (see `power.rs`'s module documentation), so the
    /// induction step needs only [`Self::mul_assoc`] to regroup, matching
    /// the house idiom `derivative.rs::pow_two_equiv_sq` and
    /// `power.rs::declare_pow_nonneg` already use for the same reduction.
    /// The closing combination with [`Self::uniformly_continuous_on`] and
    /// the Archimedean property to reach `CReal.ivt_approx` (`∀ e : Nat, ∃
    /// x, …`) is **not** built here: it needs a quantitative bound relating
    /// `pow x n` (`0 ≤ x < 1`) to a `natDivSucc`-shaped rational threshold —
    /// the "geometric-decay-dominates-harmonic-rate estimate this
    /// development does not yet build" that [`Self::geom_sum_bounded`]'s own
    /// neighbourhood already flags as missing, not a gap this file's own
    /// construction leaves behind.
    pub ivt_iter: NameId,
    /// `CReal.ivt_approx : ∀ F a b, UniformlyContinuousOn F a b → le a b →
    /// le (F a) zero → le zero (F b) → ∀ e : Nat, ∃ x, le a x ∧ le x b ∧
    /// le (abs (F x)) (ofRat (natDivSucc 1 e))` (`creal/ivt.rs`) — the
    /// **constructive approximate Intermediate Value Theorem** (Spivak ch.
    /// 7), closing [`Self::ivt_iter`] against [`Self::uniformly_continuous_on`]
    /// and [`Self::pow_half_le_nat_div_succ`].
    ///
    /// Chooses the bisection depth `N` and the continuity/sign slack `eps`
    /// entirely by computation, with no search and no `Exists.rec`: `eps :=
    /// ofRat (natDivSucc 1 n)` for `n := 2·e + 1` (so `eps + eps ~
    /// ofRat (natDivSucc 1 e)` via [`RatPrelude::nat_div_succ_add`] then
    /// [`RatPrelude::nat_div_succ_halve`]); `delta := ` the continuity
    /// modulus at `n`; and `N := M·delta + c` for `c := CReal.bound (b −
    /// a)`, `M := c + 1` — [`RatPrelude::nat_div_succ_scale`]'s own index
    /// shape, chosen so `M · natDivSucc 1 N = natDivSucc 1 delta` is an
    /// **equality**, not merely a bound. `CReal.bound` is a total computable
    /// projection (`Self::bound`), so this needs no Archimedean-property
    /// `Exists` unwrap either: the same non-existential bound
    /// [`Self::archimedean`] is built from is reproduced directly against
    /// `b − a`.
    ///
    /// The witness returned is always the final bracket's RIGHT endpoint:
    /// with the sign invariant `F P ≤ eps`, `−eps ≤ F Q` and continuity
    /// giving `|F Q − F P| ≤ eps`, `F Q ≤ F P + eps ≤ eps + eps` and `−eps ≤
    /// F Q` already, so `|F Q| ≤ eps + eps = ofRat (natDivSucc 1 e)`
    /// directly, no case split on any sign.
    pub ivt_approx: NameId,
    /// `CReal.ivt_bisect : (CReal → CReal) → CReal → CReal → Nat → Nat →
    /// Bool → CReal` (`creal/ivt.rs`) — a **data-valued** bisection,
    /// replacing `ivt_iter`'s `Exists`-wrapped bracket with one actually
    /// computed by `Nat.rec` into `Sort 1` (legal because `Nat`'s own sort is
    /// nonzero — `docs/mathematics-2026-08/diary-exact-root-obstruction.md`).
    ///
    /// Three design choices, all forced by what is and is not computable
    /// here:
    /// - **`eps` is the explicit `Nat` `n`** (`eps_n := ofRat (natDivSucc 1
    ///   n)`), not an arbitrary `CReal` — an arbitrary real carries no
    ///   `Nat` a construction could sample at, the same obstruction
    ///   `CReal.inv`'s explicit modulus already works around.
    /// - **The per-step branch is read off a RATIONAL sample**, not `F`'s
    ///   sign: at the FIXED index `j := succ (2*n)` (same `j` every step —
    ///   the invariant's slack never shrinks, matching `ivt_iter`, not
    ///   `ivt_approx`), `Rat.ble (seq (F m) j) (natDivSucc 1 j)` is a
    ///   genuine `Bool` (`Rat.ble`, not `Rat.le_or_lt`), so `Bool.rec` may
    ///   select a `CReal` freely (`sqrt.rs`'s `natSqrt` is the precedent for
    ///   this move one type down).
    /// - **The bracket carrier is `Bool → CReal`**, not a new `Prod`/`Sigma`
    ///   (this kernel has neither) and not two independently-recursing
    ///   `Nat → CReal` functions (which would need the SAME pairing anyway
    ///   to compute next-step's midpoint from both current endpoints). One
    ///   `Nat.rec` produces the pair at each step; applying it to
    ///   `Bool.false`/`Bool.true` reads off the two endpoints —
    ///   [`Self::ivt_bisect_lo`]/[`Self::ivt_bisect_hi`] are exactly those
    ///   two applications, packaged as their own one-line definitions.
    ///
    /// The invariant spec theorem this comment once called "a separate,
    /// not-yet-landed slice" is [`Self::ivt_bisect_invariant`], landed; and
    /// the bracket is what [`Self::ivt_exact_root`] runs on, so this
    /// construction is now load-bearing for an EXACT root rather than a
    /// promising shape.
    pub ivt_bisect: NameId,
    /// `CReal.ivt_bisect_lo : (CReal → CReal) → CReal → CReal → Nat → Nat →
    /// CReal := fun F P Q n k => ivt_bisect F P Q n k Bool.false` — the
    /// lower endpoint after `k` bisection steps at slack index `n`. See
    /// [`Self::ivt_bisect`].
    pub ivt_bisect_lo: NameId,
    /// `CReal.ivt_bisect_hi : (CReal → CReal) → CReal → CReal → Nat → Nat →
    /// CReal := fun F P Q n k => ivt_bisect F P Q n k Bool.true` — the upper
    /// endpoint after `k` bisection steps at slack index `n`. See
    /// [`Self::ivt_bisect`].
    pub ivt_bisect_hi: NameId,
    /// `CReal.ivt_bisect_invariant : ∀ F P0 Q0 n, le P0 Q0 → le (F P0) (ofRat
    /// (natDivSucc 1 n)) → le (neg (ofRat (natDivSucc 1 n))) (F Q0) → ∀ k, le
    /// P0 (ivt_bisect_lo F P0 Q0 n k) ∧ le (ivt_bisect_lo F P0 Q0 n k)
    /// (ivt_bisect_hi F P0 Q0 n k) ∧ le (ivt_bisect_hi F P0 Q0 n k) Q0 ∧ le (F
    /// (ivt_bisect_lo F P0 Q0 n k)) (ofRat (natDivSucc 1 n)) ∧ le (neg (ofRat
    /// (natDivSucc 1 n))) (F (ivt_bisect_hi F P0 Q0 n k)) ∧ Equiv (add
    /// (ivt_bisect_hi F P0 Q0 n k) (neg (ivt_bisect_lo F P0 Q0 n k))) (mul
    /// (add Q0 (neg P0)) (pow (ofRat (natDivSucc 1 1)) k))` (`creal/ivt.rs`)
    /// — the **invariant spec theorem** [`Self::ivt_bisect`]'s own doc
    /// comment names as not-yet-landed: the concrete, data-valued bracket
    /// [`Self::ivt_bisect_lo`]/[`Self::ivt_bisect_hi`] computes satisfies the
    /// SAME six-part invariant [`Self::ivt_step`]/[`Self::ivt_iter`] prove
    /// for the existentially-quantified bracket, for the FIXED slack `eps_n
    /// := ofRat (natDivSucc 1 n)`.
    ///
    /// Proved by ordinary `Prop`-level induction on `k` (no `Exists.rec`
    /// needed anywhere, unlike [`Self::ivt_iter`]'s own proof, since `lo`/`hi`
    /// are already concrete data rather than an existential witness to
    /// unpack). The induction step reads the per-step branch back out of
    /// `Rat.ble (seq (F m) j) (natDivSucc 1 j) `'s `Bool` via a "remembering"
    /// `Bool.rec` (`nat_prelude/finite.rs::compact_eq_of_gt`'s own
    /// "generalize then instantiate at `bool_refl`" idiom): the branch's
    /// `Bool` alone forgets *why* it took that value, so the proof
    /// generalizes over `Eq Bool br b` before casing, giving each branch a
    /// genuine hypothesis `br = true`/`br = false` to feed
    /// [`crate::RatPrelude::le_of_ble_eq_true`]/[`crate::RatPrelude::ble_eq_true_of_le`],
    /// then [`Self::rat_approx_upper`]/[`Self::rat_approx_lower`] convert the
    /// resulting rational bound back to the `CReal` sign fact `ivt_step`'s
    /// own invariant needs.
    pub ivt_bisect_invariant: NameId,
    /// `CReal.ivt_bisect_diag : (CReal → CReal) → CReal → CReal → Nat → Bool
    /// → CReal` (`creal/ivt.rs`) — the **diagonal** bisection: the SAME
    /// `Nat.rec` shape as [`Self::ivt_bisect`], but with the external slack
    /// parameter `n` **removed**. Each step samples `F` at its OWN recursion
    /// depth `j` (`Nat.rec`'s step closure already receives `j`; `ivt_bisect`
    /// discarded it and used a fixed outer `n` instead) — sample index `succ
    /// (2*j)`, threshold `natDivSucc 1 (succ (2*j))`, exactly
    /// `ivt.rs`'s own `bisect_sample_index` helper applied to `j` in place of
    /// a captured `n`. "Diagonal" names this precisely: depth and slack index
    /// literally coincide at every step, one bisection run with no second
    /// `Nat` parameter, per
    /// `docs/mathematics-2026-08/diary-exact-root-obstruction.md`'s "diagonal
    /// bisection with shrinking slack" addendum.
    ///
    /// **Landed as the data-valued construction and a concrete reduction
    /// test only.** The diary addendum this declaration accompanies records
    /// a verified NEGATIVE result: for `F := id` on `[−1, 2]`, this
    /// construction's lower endpoint freezes at `1/2` after its very first
    /// step (`F(1/2) = 1/2 ≤ thresh₀ = 1/2` is accepted once, at the
    /// COARSEST slack, and never re-examined against a tighter one), so the
    /// bracket converges to `L = 1/2` with `F(L) = 1/2 ≠ 0` even though the
    /// true root is `0` — a fixed-point, kernel-verified rational
    /// computation, not an informal argument. No joint width/slack invariant
    /// closes over this bracket to an exact root in general, and
    /// [`Self::ivt_bisect_invariant`]'s route (an EXTERNAL fixed `n`,
    /// re-instantiated at `n := k` for each `k` from scratch) fails for the
    /// opposite reason: different `k` take different, non-nested
    /// trajectories (verified: `k=3` and `k=4` brackets on the same `F`/
    /// bracket above are not nested). Both routes to an exact IVT root from
    /// this bisection are closed for general `F`; see the diary for the full
    /// derivation and both counterexamples.
    ///
    /// **"For general `F`" is the operative phrase, and it stays true.**
    /// [`Self::ivt_exact_root`] does reach an exact root, from
    /// [`Self::ivt_bisect`] (the EXTERNAL-slack construction, not this
    /// diagonal one) and one extra hypothesis: a uniformly positive
    /// derivative. Neither counterexample above is affected — both are
    /// derivative-free — and neither route named here is the one that
    /// worked: the sequence is re-instantiated at a fresh slack per accuracy
    /// and its convergence comes from the derivative bound, never from
    /// nesting.
    pub ivt_bisect_diag: NameId,
    /// `CReal.ivt_bisect_diag_lo : (CReal → CReal) → CReal → CReal → Nat →
    /// CReal := fun F P Q k => ivt_bisect_diag F P Q k Bool.false` — the
    /// lower endpoint after `k` diagonal bisection steps. See
    /// [`Self::ivt_bisect_diag`].
    pub ivt_bisect_diag_lo: NameId,
    /// `CReal.ivt_bisect_diag_hi : (CReal → CReal) → CReal → CReal → Nat →
    /// CReal := fun F P Q k => ivt_bisect_diag F P Q k Bool.true` — the
    /// upper endpoint after `k` diagonal bisection steps. See
    /// [`Self::ivt_bisect_diag`].
    pub ivt_bisect_diag_hi: NameId,
    /// `CReal.ivt_bisect_approx : ∀ F a b, UniformlyContinuousOn F a b →
    /// le a b → le (F a) zero → le zero (F b) → ∀ e : Nat,
    /// And (le a (ivt_bisect_hi F a b (Nat.succ (Nat.mul 2 e)) K))
    ///     (And (le (ivt_bisect_hi F a b (Nat.succ (Nat.mul 2 e)) K) b)
    ///          (le (abs (F (ivt_bisect_hi F a b (Nat.succ (Nat.mul 2 e)) K)))
    ///              (ofRat (natDivSucc 1 e))))`, where
    /// `K := Nat.add (Nat.mul (Nat.succ (bound (add b (neg a))))
    /// (ucModulus F a b u (Nat.succ (Nat.mul 2 e)))) (bound (add b (neg a)))`
    /// (`creal/ivt.rs`) — **[`Self::ivt_approx`] with the `Exists` removed.**
    ///
    /// [`Self::ivt_approx`] quantifies its witness existentially because
    /// [`Self::ivt_iter`]'s bracket is existential, so nothing outside that
    /// proof can name the point — and a *sequence* of such points cannot be
    /// formed at all, since `∀ e, ∃ x` → `Nat → CReal` is an `Exists`
    /// elimination into a `Type`-valued target. This states the identical
    /// bound about the NAMED point [`Self::ivt_bisect_hi`] computes, at the
    /// depth [`Self::ivt_approx`]'s own schedule already chose, so
    /// `fun e => ivt_bisect_hi F a b (Nat.succ (Nat.mul 2 e)) K` is an
    /// ordinary lambda.
    ///
    /// One estimate, not two: `creal/ivt.rs`'s `approx_endpoint_bound` is
    /// shared verbatim by both declarations, applied here to the concrete
    /// pair [`Self::ivt_bisect_invariant`] supplies instead of to
    /// [`Self::ivt_iter`]'s eliminated witness.
    pub ivt_bisect_approx: NameId,
    /// `CReal.abs_diff_le_of_small_image : ∀ F F' a b, HasDerivativeOn F F' a
    /// b → ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
    /// ∀ epsX epsY x y, le a x → le x b → le a y → le y b →
    /// le (abs (F x)) epsX → le (abs (F y)) epsY →
    /// le (abs (add x (neg y))) (mul (ofNat (Nat.succ (Nat.succ (Nat.mul 2
    /// k)))) (add epsX epsY))` (`creal/ivt.rs`) — **two points of `[a,b]`
    /// whose `F`-values are small are close**, with NO hypothesis ordering
    /// them and no [`Self::apart`] witness.
    ///
    /// The two accuracies are kept separate rather than shared: a Cauchy
    /// caller comparing indices `m` and `n` has `1/(m+1)` and `1/(n+1)`, and
    /// this shape puts its conclusion one [`Self::of_rat_add`] away from the
    /// `natDivSucc K m + natDivSucc K n` form [`Self::cauchy`] states.
    ///
    /// This is the Cauchy criterion an exact IVT root needs: the bisection
    /// brackets at two different accuracies are not nested and cannot be
    /// ordered ([`Self::ivt_bisect_diag`]'s own doc records the verified
    /// non-nesting), so [`Self::diff_le_of_strict_mono_magnitude`] — which
    /// takes `le x y` — and [`Self::inverse_lipschitz_of_pos_deriv`] — which
    /// takes `Apart x y` — are both out of reach at the point of use.
    ///
    /// `docs/mathematics-2026-08/diary-exact-root-obstruction.md` proposed
    /// closing that gap through the LATTICE, at the pair `(min x y, max x y)`.
    /// That does not close: the bound it yields mentions
    /// `abs (F (min x y))`, and recovering `le (abs (F (min x y))) eps` needs
    /// a LOWER bound on `F (min x y)`, which the meet-semilattice interface
    /// ([`Self::min_le_left`], [`Self::min_le_right`], [`Self::le_min`]) plus
    /// monotonicity cannot supply — every one of them bounds it ABOVE. The
    /// route that does close is [`Self::lt_cotrans`] at the fixed strict pair
    /// `(zero, 1/(e+1))`, evaluated at the difference: one disjunct hands
    /// back the ordering `diff_le_of_strict_mono_magnitude` wants, the other
    /// gives the goal outright, and [`Self::le_of_forall_le_add_small`]
    /// removes the slack. See `creal/ivt.rs`'s own section header.
    pub abs_diff_le_of_small_image: NameId,
    /// `CReal.ivt_bisect_cauchy_bound : ∀ F F' a b, HasDerivativeOn F F' a b →
    /// ∀ (u : UniformlyContinuousOn F a b), le a b → le (F a) zero →
    /// le zero (F b) → ∀ k, (∀ z, le a z → le z b →
    /// le (ofRat (natDivSucc 1 k)) (F' z)) → ∀ m n : Nat,
    /// le (abs (add (X m) (neg (X n))))
    ///    (ofRat (Rat.add (natDivSucc C m) (natDivSucc C n)))`, where
    /// `X e := ivt_bisect_hi F a b (Nat.succ (Nat.mul 2 e)) K` is
    /// [`Self::ivt_bisect_approx`]'s named point and
    /// `C := Nat.succ (Nat.succ (Nat.mul 2 k))` (`creal/ivt.rs`) — **the
    /// exact IVT root's Cauchy estimate, at the `CReal` level.**
    ///
    /// [`Self::ivt_bisect_approx`] bounds `abs (F (X e))` by `1/(e+1)` at a
    /// NAMED point; [`Self::abs_diff_le_of_small_image`] turns two such
    /// bounds into closeness of the points themselves, with no ordering and
    /// no [`Self::apart`] — the two things a bisection cannot supply.
    ///
    /// **What separates this from [`Self::cauchy`] is one bridge, and it is
    /// general rather than IVT-specific.** This is the REAL-valued
    /// inequality; `Cauchy f` is stated on the canonical rational SAMPLES,
    /// `Within (seq (f m) m − seq (f n) n) (natDivSucc K m + natDivSucc K n)`.
    /// Crossing costs [`Self::within_of_two_sided_le`] (real bound → `Within`
    /// at a shared index) followed by [`Self::shared_index_to_canonical`]
    /// (shared index → the two canonical indices), plus the rational
    /// bookkeeping that folds the resulting seven-term bound back to the
    /// two-term rate. No such bridge exists in either direction as a
    /// standalone lemma — `close_within_of_within` and
    /// `close_within_of_within_indexed` run the OTHER way — and
    /// `riemannSum_cauchy`'s own doc comment records the identical gap for
    /// the integral. One lemma closes both.
    pub ivt_bisect_cauchy_bound: NameId,
    /// `CReal.cauchy_of_abs_diff_le : ∀ (f : Nat → CReal) (K : Nat),
    /// (∀ m n, le (abs (add (f m) (neg (f n))))
    ///           (ofRat (Rat.add (natDivSucc K m) (natDivSucc K n)))) →
    /// Cauchy f` (`creal/ivt.rs`) — **the REAL-valued Cauchy criterion,
    /// bridged to [`Self::cauchy`]'s canonical-sample form.**
    ///
    /// Every estimate in this development that establishes a Cauchy sequence
    /// produces a real inequality about `abs (f m − f n)`; [`Self::cauchy`]
    /// is stated on the rational SAMPLES `seq (f m) m − seq (f n) n`. Nothing
    /// crossed that gap in this direction — [`Self::close_within_of_within`]
    /// and [`Self::close_within_of_within_indexed`] run the other way — and
    /// `riemannSum_cauchy`'s own doc records the same gap for the integral.
    ///
    /// [`Self::within_of_two_sided_le`] reaches a `Within` at an arbitrary
    /// SHARED index; [`Self::shared_index_to_canonical`] moves to the two
    /// canonical ones at the cost of two regularity legs. **The index choice
    /// `j := 3m+2` makes the whole seven-term bound an EQUALITY**, not a
    /// chain of widenings: `Rat.natDivSucc_halve` collapses the two
    /// `1/(2j+2)` legs to `1/(j+1)`, `Rat.natDivSucc_add` fuses that with the
    /// `2/(j+1)` slack to `3/(j+1)`, and `Rat.natDivSucc_scale 2 m` makes
    /// `3/(j+1)` exactly `1/(m+1)`. The only inequality in the proof is the
    /// final `Rat.natDivSucc_le_add_left` raising one numerator from `K+1` to
    /// the shared witness `K+2`.
    ///
    /// Filed in `creal/ivt.rs` because the exact IVT root is what first
    /// needed it; nothing in the statement or the proof mentions the IVT.
    pub cauchy_of_abs_diff_le: NameId,
    /// `CReal.scaledCauchy_of_abs_diff_le : ∀ (f : Nat → CReal) (K : Nat),
    /// (∀ m n, le (abs (add (f m) (neg (f n))))
    ///           (ofRat (Rat.add (natDivSucc K m) (natDivSucc K n)))) →
    /// ∀ m n, Within (seq (f m) m − seq (f n) n)
    ///   (Rat.add (natDivSucc (Nat.add K 2) m) (natDivSucc (Nat.add K 2) n))`
    /// (`creal/ivt.rs`) — [`Self::cauchy_of_abs_diff_le`]'s own body, stopping
    /// one step short of the `Exists` intro.
    ///
    /// **The reason it is separate at all is kernel fact 2.**
    /// [`Self::regular_of_scaled_cauchy`] needs the `(K, per-pair)` pair as
    /// DATA, and `Exists.rec` is `Prop`-only, so a `Cauchy f` witness can
    /// never give it back. Any construction that turns a real-valued Cauchy
    /// estimate into an actual `CReal` — [`Self::sup_on`] is the first — needs
    /// the pair before the existential closes. Extracted rather than
    /// duplicated beside the caller: the kernel would verify two copies of one
    /// 300-line seven-term bound just as happily, and they would then have to
    /// stay in sync.
    ///
    /// `K + 2`, not `K`, is what the index shift `j := 3m+2` costs — see
    /// [`Self::cauchy_of_abs_diff_le`] for the accounting.
    pub scaled_cauchy_of_abs_diff_le: NameId,
    /// `CReal.converges_of_abs_diff_le : ∀ (f : Nat → CReal) (L : CReal)
    /// (K : Nat), (∀ n, le (abs (add (f n) (neg L)))
    ///                    (ofRat (Rat.natDivSucc K n))) →
    /// Converges f L` (`creal/uniform_convergence.rs`) — **the REAL-valued
    /// convergence criterion, bridged to [`Self::converges`]'s
    /// canonical-sample form**, and the `Converges` sibling of
    /// [`Self::cauchy_of_abs_diff_le`].
    ///
    /// `UniformConvergesOn.spec` — and so every `weierstrassMTest` consumer —
    /// produces a `close_within`-shaped real inequality about
    /// `abs (f n − L)`; [`Self::converges`] is stated on the rational SAMPLES
    /// `seq (f n) n − seq L n`. Nothing crossed that gap in this direction:
    /// [`Self::close_within_of_within`] and
    /// [`Self::close_within_of_within_indexed`] run the other way, and
    /// [`Self::converges_of_close`]/[`Self::converges_of_scaled_cauchy`] both
    /// already start from a `Within`.
    ///
    /// [`Self::within_of_two_sided_le`] reaches a `Within` at an arbitrary
    /// SHARED index; [`Self::shared_index_to_canonical`] — which already IS
    /// the `CReal.add` index-shift regularity bridge, generically in both
    /// reals and in the bound function — moves to the canonical one. **The
    /// index choice `j := 3n+2` makes the whole six-term bound an EQUALITY**:
    /// `Rat.natDivSucc_halve` collapses the two `1/(2j+2)` legs to `1/(j+1)`,
    /// `Rat.natDivSucc_add` fuses that with the `2/(j+1)` slack to `3/(j+1)`,
    /// and `Rat.natDivSucc_scale 2 n` makes `3/(j+1)` exactly `1/(n+1)`.
    /// Unlike [`Self::cauchy_of_abs_diff_le`], whose two canonical indices
    /// differ and so needs a final `Rat.natDivSucc_le_add_left` widening,
    /// **this proof contains no inequality at all** — the witness is exactly
    /// `Nat.add K 3`.
    ///
    /// There is no low-index obligation: every step is an identity in `n`, so
    /// `n = 0` is just the instance where all four denominators are `1`.
    pub converges_of_abs_diff_le: NameId,
    /// `CReal.ivt_bisect_cauchy : ∀ F F' a b, HasDerivativeOn F F' a b →
    /// ∀ (u : UniformlyContinuousOn F a b), le a b → le (F a) zero →
    /// le zero (F b) → ∀ k, (∀ z, le a z → le z b →
    /// le (ofRat (natDivSucc 1 k)) (F' z)) →
    /// Cauchy (fun e => ivt_bisect_hi F a b (Nat.succ (Nat.mul 2 e)) K)`
    /// (`creal/ivt.rs`) — [`Self::ivt_bisect_cauchy_bound`] composed with
    /// [`Self::cauchy_of_abs_diff_le`].
    ///
    /// **The shape is the point, not the estimate.** The sequence is an
    /// ordinary `Nat → CReal` lambda, so it can be the argument of
    /// [`Self::cauchy`], [`Self::converges`], [`Self::converges_of_cauchy`],
    /// [`Self::converges_lower_bound`] and
    /// [`Self::converges_comp_eventually`] — none of which a sequence of
    /// [`Self::ivt_approx`] witnesses could ever be, since `∀ e, ∃ x` does
    /// not eliminate into a `Type`. That was the first obstruction recorded
    /// in `docs/mathematics-2026-08/diary-exact-root-obstruction.md`.
    pub ivt_bisect_cauchy: NameId,
    /// `CReal.ivt_exact_root : ∀ F F' a b, HasDerivativeOn F F' a b →
    /// UniformlyContinuousOn F a b → le a b → le (F a) zero → le zero (F b) →
    /// ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
    /// ∃ c, le a c ∧ (le c b ∧ Equiv (F c) zero)` (`creal/ivt.rs`) — **an
    /// EXACT root**: `Equiv (F c) zero` outright, not
    /// [`Self::ivt_approx`]'s `|F c| ≤ eps` per accuracy.
    ///
    /// The classical IVT is genuinely unavailable constructively (this
    /// file's module documentation says why, and nothing here decides the
    /// sign of a real). What unlocks the exact statement is ONE extra
    /// hypothesis, a uniformly positive derivative: it does not make any
    /// sign decidable, it makes the root unique WITH A MODULUS, which is
    /// what turns a sequence of approximate roots into a Cauchy sequence.
    ///
    /// Five steps, each a named declaration:
    /// [`Self::ivt_bisect_hi`] (the sequence, as data),
    /// [`Self::ivt_bisect_approx`] (`|F (X e)| ≤ 1/(e+1)` at a NAMED point),
    /// [`Self::ivt_bisect_cauchy`] (via
    /// [`Self::abs_diff_le_of_small_image`] and
    /// [`Self::cauchy_of_abs_diff_le`]), [`Self::converges_of_cauchy`] with
    /// [`Self::converges_lower_bound`]/[`Self::converges_upper_bound`] for
    /// the domain conjuncts, and [`Self::converges_comp_eventually`] plus
    /// [`Self::equiv_zero_of_small`] for `Equiv (F L) zero`.
    ///
    /// Every `Exists` eliminated here has a `Prop` target, which is the
    /// elimination this kernel permits — the wall
    /// `docs/mathematics-2026-08/diary-exact-root-obstruction.md` records
    /// only ever blocked `Type`-valued elimination, and the bisection being
    /// DATA is what keeps the sequence itself out of that case.
    pub ivt_exact_root: NameId,
    /// `creal/deriv_unique.rs`'s own name, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.deriv_unique.has_derivative_unique` and documented in
    /// [`DerivUniqueNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub deriv_unique: DerivUniqueNames,
    /// `CReal.fermat_interior_extremum : ∀ F F' lo hi, HasDerivativeOn F F'
    /// lo hi → ∀ c, lt lo c → lt c hi → (∀ x, le lo x → le x hi →
    /// le (F x) (F c)) → Equiv (F' c) zero` (`creal/fermat.rs`) — Fermat's
    /// interior-extremum theorem (Spivak ch. 11, Thm 1). Unlike the classical
    /// statement, this needs **no** case split and **no** existence argument:
    /// the maximum point `c` is a hypothesis, not a conclusion, so the one
    /// genuinely non-constructive ingredient of the classical theorem (the
    /// Extreme Value Theorem, which produces the maximiser — see
    /// `creal/extreme_value.rs`) never enters. The route is direct: for each
    /// accuracy `e`, pick a rational gap `q` small enough to (a) keep `c ± q`
    /// inside `[lo, hi]` (from the two `lt` witnesses via `gap_elim`) and (b)
    /// satisfy `hd_spec`'s own modulus at `e`; the max hypothesis bounds
    /// `F(c±q) - F(c)` above by zero, and `hd_spec` at `c` and `c±q` gives a
    /// two-sided bound on `F'(c)` of exactly `1/(e+1)`, for every `e` —
    /// closed by `CReal.equiv_zero_of_small`.
    pub fermat_interior_extremum: NameId,
    /// `CReal.rolle_interiorExtremum : ∀ F F' lo hi, HasDerivativeOn F F' lo
    /// hi → Equiv (F lo) (F hi) → ∀ c, lt lo c → lt c hi → (Or (∀ x, le lo x
    /// → le x hi → le (F x) (F c)) (∀ x, le lo x → le x hi → le (F c) (F
    /// x))) → Equiv (F' c) zero` (`creal/rolle.rs`) — Rolle's theorem (Spivak
    /// ch. 11, Thm 2) taking the extremum point `c` as a HYPOTHESIS, exactly
    /// as [`Self::fermat_interior_extremum`] does. The max branch of the
    /// `Or` IS [`Self::fermat_interior_extremum`] applied directly; the min
    /// branch applies it to `neg ∘ F` (via [`Self::has_derivative_neg`]) and
    /// undoes the negation. `Equiv (F lo) (F hi)` is a FAITHFUL hypothesis
    /// (kept so this reads as Rolle's, not a coincidental Fermat corollary)
    /// but, like `fermat_interior_extremum`'s own hypotheses, is never
    /// consumed by the proof — the classical theorem's one non-constructive
    /// step is PRODUCING the extremum (the Extreme Value Theorem;
    /// `creal/extreme_value.rs` shows this kernel cannot do that in
    /// general), and taking the extremum as given is what makes this row
    /// unconditionally constructive, at the cost of being close to a thin
    /// wrapper over Fermat — see `creal/rolle.rs`'s module documentation for
    /// the full accounting, including why the UNRESTRICTED (existential)
    /// form is NOT landed here.
    pub rolle_interior_extremum: NameId,
    /// `creal/mvt.rs`'s own name, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.mvt.mvt_interior_extremum` and documented in
    /// [`MvtNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub mvt: MvtNames,
    /// `CReal.mesh_le_of_ge : ∀ a b outer m, le a b → Nat.le ((Nat.succ
    /// (bound (add b (neg a))))*outer + bound (add b (neg a))) m → le (mul
    /// (add b (neg a)) (ofRat (natDivSucc 1 m))) (ofRat (natDivSucc 1
    /// outer))` (`creal/integral.rs`) — the ARCHIMEDEAN RESCALING
    /// `UniformlyContinuousOn.spec` needs: turning the Riemann-sum mesh width
    /// `Δ_m := (b−a)·natDivSucc(1,m)` into a bound of the exact rational
    /// shape `natDivSucc 1 outer` that spec expects, for every block count
    /// `m` at or past a computed threshold. No existential elimination: the
    /// threshold is read directly off `CReal.bound`. See that file's own
    /// module documentation for the derivation and for what still separates
    /// this from `riemannSum_cauchy`.
    pub mesh_le_of_ge: NameId,
    /// `CReal.meshScaledLeOfGe : ∀ a b outer m k0, le a b → Nat.le
    /// ((Nat.succ (bound (add b (neg a))))*(Nat.mul (Nat.succ k0) outer +
    /// k0) + bound (add b (neg a))) m → le (mul (ofNat (Nat.succ k0)) (mul
    /// (add b (neg a)) (ofRat (natDivSucc 1 m)))) (ofRat (natDivSucc 1
    /// outer))` (`creal/integral.rs`) — the SCALED analogue of
    /// [`Self::mesh_le_of_ge`] that `crossing.rs`'s `crossingClose` needs
    /// (its own doc comment, and `integral.rs`'s 2026-08-27 module doc
    /// entry, name this exactly): bounds `k·Δ_m` for an explicit Nat
    /// multiplier `k := Nat.succ k0`, never a fixed literal, rather than
    /// `Δ_m` itself.
    ///
    /// Reuses [`Self::mesh_le_of_ge`] WHOLESALE at a substituted `outer' :=
    /// k*outer + k0` (so ITS OWN threshold, unfolded here, gives `Δ_m ≤
    /// 1/(outer'+1)` rather than `≤ 1/(outer+1)`), then multiplies by the
    /// nonneg `k` and collapses `k·(1/(outer'+1))` back to `1/(outer+1)`
    /// with the SAME `magnitude_times_frac_eq_outer` private helper
    /// `mesh_le_of_ge`'s own proof uses, at `c := k0`, `magnitude := k`,
    /// `deep := outer'` — exactly `Rat.natDivSucc_scale`'s required shape
    /// (`deep = mul(magnitude,outer)+c`), so the identity is free. `k :=
    /// Nat.succ k0` throughout (never a bare Nat fvar with a `0 < k`
    /// hypothesis) for the same reason `mesh_le_of_ge`'s own `magnitude :=
    /// Nat.succ c` is: the reused private helper pattern-matches a
    /// `Nat.succ` structurally applied, not merely a positivity hypothesis.
    /// See `creal/integral.rs`.
    pub mesh_scaled_le_of_ge: NameId,
    /// `CReal.fineSample_in_bounds : ∀ a b m n i j, le a b → Nat.le i m →
    /// Nat.lt j (Nat.succ n) → And (le a x) (le x b)`, `x := add
    /// (sample_point a delta_m i) (mul (ofNat j) delta_fine)`, `delta_m :=
    /// (b−a)·natDivSucc(1,m)`, `delta_fine := delta_m·natDivSucc(1,n)`
    /// (`creal/integral.rs`) — the fine-sample placement lemma
    /// `riemannSum_cauchy`'s per-block fold needs: every FINE sample point
    /// `x` inside coarse block `i` (`i ≤ m`, so `i` indexes one of
    /// `riemannSum`'s `Nat.succ m` coarse blocks) lies in `[a, b]`, for every
    /// fine sub-index `j < Nat.succ n`. `riemannSum_sample_in_bounds` /
    /// `subdivisionPoint_in_bounds` only place the COARSE sample points
    /// themselves; this is the one-index-shift generalization those two
    /// theorems do not cover. Built from TWO calls to
    /// `subdivisionPoint_in_bounds` (at coarse indices `i` and `Nat.succ i`,
    /// bracketing the block `[base, base+delta_m]`) plus the same
    /// nonneg/bounded-offset argument `sample_offset_bound` uses for its own
    /// fine term. Called from `creal.rs`'s pipeline AFTER
    /// `monotone::declare_monotone_of_nonneg_deriv_all` (for
    /// `CReal.subdivisionPoint_in_bounds`).
    pub fine_sample_in_bounds: NameId,
    /// `CReal.fineSample_close : ∀ F a b e m n i j, le a b →
    /// UniformlyContinuousOn F a b → Nat.le i m → Nat.lt j (Nat.succ n) →
    /// Nat.le deep m → close_within (F fine_j) (F base_i) (Rat.natDivSucc 1
    /// e)`, `deep := (Nat.succ (bound (add b (neg a))))·(modulus F a b u e)
    /// plus bound (add b (neg a))` (`creal/integral.rs`) — roadmap step 2
    /// toward `riemannSum_cauchy`: EVERY fine sample point inside coarse
    /// block `i` is within `1/(e+1)` of that block's own coarse value
    /// `F(base_i)`, once the coarse block count `m` clears the Archimedean
    /// threshold `deep` relative to `F`'s modulus of uniform continuity at
    /// target precision `e`. Built from [`Self::mesh_le_of_ge`],
    /// [`Self::fine_sample_in_bounds`], `UniformlyContinuousOn.spec`, and
    /// the private `sample_offset_bound` (`creal/integral.rs`). See that
    /// file's own module documentation for the derivation.
    pub fine_sample_close: NameId,
    /// `CReal.meshReciprocalMul : ∀ n m : Nat,
    /// Eq Rat (Rat.mul (Rat.natDivSucc 1 n) (Rat.natDivSucc 1 m))
    ///        (Rat.natDivSucc 1 (Nat.add (Nat.add (Nat.mul n m) n) m))`
    /// (`creal/integral.rs`) — refining a partition of `succ m` coarse
    /// pieces into `succ n` further pieces each gives a fine mesh factor
    /// EXACTLY equal (not merely close) to the single-partition factor at
    /// `m_prime := ((n·m)+n)+m`, the same witness [`Self::of_nat_add`]'s
    /// sibling `succ_mul_succ` computes (`Nat.succ m_prime` is
    /// definitionally `(Nat.succ n)·(Nat.succ m)`). Via
    /// `RatPrelude::normalize_mul_normalize` plus pure defeq — no rewrite
    /// step. Toward `riemannSum_cauchy`'s common refinement; see
    /// `integral.rs`'s module documentation.
    pub mesh_reciprocal_mul: NameId,
    /// `CReal.equivAbsDiffLe : ∀ x y : CReal, Equiv x y → ∀ e : Nat,
    /// le (abs (add x (neg y))) (embed (Rat.natDivSucc 1 e))`
    /// (`creal/integral.rs`) — two REAL-EQUAL numbers are within ANY chosen
    /// rational bound of each other, with no Archimedean threshold on `e`:
    /// `Equiv` already gives arbitrary precision for free. Via `le_of_equiv`
    /// (both directions), `add_le_add`/`add_neg`/`le_congr`, and a
    /// cancellation identity showing `neg (add x (neg y))` and `add y (neg
    /// x)` are both additive inverses of `add x (neg y)`. Toward
    /// `riemannSum_cauchy`'s common refinement: promotes "the global fine
    /// sample point IS the local block sample point" (an exact `Equiv`) into
    /// the explicit bound `UniformlyContinuousOn.spec` needs as a
    /// hypothesis.
    pub equiv_abs_diff_le: NameId,
    /// `CReal.samplePoint_reblock : ∀ a b : CReal, ∀ n m i j : Nat, Equiv
    /// (sample_point a delta_m_prime globalIdx) (sample_point base_i
    /// delta_fine j)` (`creal/integral.rs`) — roadmap step 1 toward
    /// `riemannSum_cauchy`'s common refinement: `CReal.sumRange_reblock`'s
    /// RAW global fine index sample point IS (an exact, UNCONDITIONAL
    /// `Equiv`, no bound on `i`/`j` needed) the LOCAL per-block sample point
    /// `CReal.fineBlockSum_close`'s own sum uses, `m_prime :=
    /// ((n·m)+n)+m` ([`Self::mesh_reciprocal_mul`]'s own witness),
    /// `globalIdx := Nat.add (Nat.mul (Nat.succ n) i) j`. Built from
    /// [`Self::mesh_reciprocal_mul`] (the exact mesh identity),
    /// [`Self::of_nat_add`]/[`Self::of_nat_mul`] (splitting the global
    /// index) and [`Self::mesh_count_width`] (cancelling the `Nat.succ n`
    /// factor). See `integral.rs`'s module documentation and this
    /// declaration's own section header comment.
    pub sample_point_reblock: NameId,
    /// `CReal.reblockBlock_eq_fineBlockSum : ∀ F a b m n i, le a b → Nat.le i
    /// m → UniformlyContinuousOn F a b → Equiv (sumRange (fun j => summand_fn
    /// F a delta_m_prime ((Nat.succ n)*i + j)) (Nat.succ n)) (sumRange
    /// (summand_fn F base_i delta_fine) (Nat.succ n))` (`creal/integral.rs`)
    /// — the per-block fold gluing [`Self::sum_range_reblock`]'s flat global
    /// sum (read at `g := summand_fn F a delta_m_prime`, exactly `riemannSum
    /// F a b m_prime`'s own summand at the REFINED total count `m_prime`) to
    /// [`Self::fine_block_sum_close`]'s per-block sum: an EXACT identity (no
    /// error term), by a bounded pointwise `Equiv`-congruence induction
    /// against a per-index derivation built from [`Self::sample_point_reblock`]
    /// (the exact sample-point identity), `Nat.mul_succ_add_lt_of_le_of_lt`
    /// (placing the global index in `Nat.succ`-shape), [`Self::equiv_abs_diff_le`]
    /// / [`Self::uc_spec`] (promoting the sample-point `Equiv` through `F` at
    /// every accuracy) and [`Self::equiv_zero_of_small`] (closing the
    /// resulting `∀ e, …` bound back to a full `Equiv`). Roadmap step 4 (the
    /// outer fold over all `Nat.succ m` coarse blocks) and step 5 (assembly
    /// into `riemannSum_cauchy`) are NOT attempted here.
    pub reblock_block_eq_fine_block_sum: NameId,
    /// `CReal.riemannSum_reblock_close : ∀ F a b e m n, le a b →
    /// UniformlyContinuousOn F a b → Nat.le deep m → And (le (riemannSum F a
    /// b m_prime) (add (riemannSum F a b m) (mul (ofNat (Nat.succ m))
    /// epsTerm))) (le (riemannSum F a b m) (add (riemannSum F a b m_prime)
    /// (mul (ofNat (Nat.succ m)) epsTerm)))` (`creal/integral.rs`), `m_prime
    /// := succ_mul_succ`'s witness (`Nat.succ m_prime` definitionally
    /// `(Nat.succ n)·(Nat.succ m)`) and `epsTerm := mul (embed (Rat.natDivSucc
    /// 1 e)) delta_m` — roadmap step 4 toward `riemannSum_cauchy`: folding
    /// [`Self::reblock_block_eq_fine_block_sum`]'s exact per-block identity
    /// (via [`Self::sum_range_reblock`], transported along `succ_mul_succ`,
    /// to glue the REFINED `riemannSum` to the reblocked sum) against
    /// [`Self::fine_block_sum_close`]'s own `≤`-bound, summed over all
    /// `Nat.succ m` coarse blocks with [`Self::sum_range_le`] +
    /// [`Self::sum_range_add`] + [`Self::sum_range_const`]. Roadmap step 5
    /// (assembling this into `riemannSum_cauchy` via
    /// [`Self::within_of_two_sided_le`]) is NOT attempted here.
    pub riemann_sum_reblock_close: NameId,
    /// `CReal.riemannSum_cauchy : ∀ F a b e n k, le a b →
    /// UniformlyContinuousOn F a b → ∀ i : Nat, Within (seq (add (riemannSum
    /// F a b m_prime) (neg (riemannSum F a b m))) i) (add (seq totalEps i)
    /// (natDivSucc 2 i))` (`creal/integral.rs`), `m := Nat.add deep k`
    /// (`deep` [`Self::riemann_sum_reblock_close`]'s own Archimedean
    /// threshold at `(F, a, b, e, u)`, `Nat.le deep m` discharged
    /// unconditionally via `Nat.le_add_right` rather than left an assumed
    /// hypothesis), `m_prime`/`totalEps` [`Self::riemann_sum_reblock_close`]'s
    /// own witness/error term at that `m` — roadmap step 5, closing the
    /// roadmap. Rearranges `riemann_sum_reblock_close`'s two-sided `≤`
    /// sandwich into the two-sided form [`Self::within_of_two_sided_le`]
    /// itself demands and applies it directly. NOT `CReal.Cauchy` in that
    /// definition's own canonical-index shape — see `integral.rs`'s own
    /// documentation for why that bridge is separate, unattempted work.
    pub riemann_sum_cauchy: NameId,
    /// `CReal.sharedIndexToCanonical : ∀ (X Y : CReal) (bound : Nat → Rat),
    /// (∀ i, Within (seq (add X (neg Y)) i) (bound i)) → ∀ p q j : Nat,
    /// Within (Rat.sub (seq X p) (seq Y q)) ((modulus p (shift j) + bound j)
    /// + modulus (shift j) q)`.
    ///
    /// **The representative-index bridge** `riemannSum_cauchy`'s own doc
    /// comment names as the one gap between it and `CReal.integral`:
    /// `riemannSum_cauchy` (and `series.rs`'s structurally analogous
    /// `sumRange` case) proves closeness of a difference at an arbitrary
    /// SHARED index; `RegularSeq`/`Cauchy` compare `X`/`Y` at their OWN,
    /// generally different, canonical indices. General in `X`, `Y` and the
    /// bound function — nothing in it is `riemannSum`-specific, so the same
    /// theorem closes `series.rs`'s analogous gap too. See
    /// `creal/integral.rs`'s `declare_shared_index_to_canonical` for the
    /// three-leg telescope and exactly what remains (an arbitrary-pair
    /// common-refinement construction) to reach `CReal.integral` itself.
    pub shared_index_to_canonical: NameId,
    /// `CReal.riemannSum_sharedAccuracyClose : ∀ F a b e k1 k2, le a b →
    /// UniformlyContinuousOn F a b → ∀ p q j1 j2 : Nat, Within
    /// (Rat.sub (seq (riemannSum F a b m1) p) (seq (riemannSum F a b m2) q))
    /// (BND1 j1 + BND2 j2)`, `m1 := Nat.add deep k1`, `m2 := Nat.add deep
    /// k2` (SAME `deep`, i.e. `m1`/`m2` are two counts both "deep enough"
    /// for the SAME chosen accuracy `e`) (`creal/integral.rs`).
    ///
    /// The common-refinement construction `riemannSum_cauchy`'s and
    /// `sharedIndexToCanonical`'s own doc comments name as the remaining gap
    /// toward `CReal.integral`: two [`Self`]-independent `Nat.succ_mul`
    /// refinements of `m1`/`m2` (`integral.rs`'s private `common_refinement`,
    /// identifying the two via `Nat.mul_comm`) land at the SAME shared
    /// refinement target, so `riemannSum_cauchy` applied twice plus
    /// `sharedIndexToCanonical` applied twice telescope `riemannSum F a b
    /// m1` and `riemannSum F a b m2` together directly, with no rewrite
    /// beyond the one `Nat.mul_comm`-derived equality that `common_refinement`
    /// itself already supplies.
    ///
    /// **Not yet `CReal.Cauchy`/`RegularSeq` for the RAW-indexed sequence
    /// `fun n => riemannSum F a b n`, and precisely why not**: this
    /// theorem's `m1`/`m2` share ONE accuracy `e`, so its bound does not
    /// shrink as `m1`/`m2` grow past the point needed for that fixed `e` —
    /// exactly the rate `CReal.Cauchy`'s existential `K` needs. Reaching
    /// that needs `e` to grow with the sequence's OWN index (reindexing via
    /// `deep` rather than comparing at raw counts) PLUS a genuinely new
    /// CReal-magnitude bound turning `riemannSum_cauchy`'s `totalEps` sample
    /// into a closed-form rational — see `creal/integral.rs`'s
    /// `declare_shared_index_to_canonical` doc comment for both pieces,
    /// sized precisely rather than gestured at.
    pub riemann_sum_shared_accuracy_close: NameId,
    /// `CReal.riemannSum_sharedAccuracyClose_at : ∀ (x y1 y2 : CReal) (bound1
    /// bound2 : Nat → Rat) (l : Nat), (∀ i, Within (sample (add x (neg y1))
    /// i) (bound1 i)) → (∀ i, Within (sample (add x (neg y2)) i) (bound2
    /// i)) → ∀ oi oj jj1 jj2, Within (sub (sample y1 oi) (sample y2 oj))
    /// (bound)` — the shared-mid-anchor "wiring" step behind
    /// [`Self::riemann_sum_shared_accuracy_close`] with `l` (the sample
    /// index shared by both [`Self::shared_index_to_canonical`]
    /// applications) and the two closeness hypotheses `h1`/`h2` genuinely
    /// `Π`-bound, rather than derived internally from
    /// `riemann_sum_cauchy`/`common_refinement`
    /// (`creal/integral.rs`'s private `common_refinement`) the way
    /// [`Self::riemann_sum_shared_accuracy_close`]'s own conclusion bakes
    /// them in. Added alongside that theorem (2026-08-27) because a
    /// consumer wanting to reason about `l` itself — e.g. how `natDivSucc(1,
    /// l)` shrinks as a mesh-refinement depth grows, toward `integral_split`
    /// — needs to name `l` as a bound variable rather than reconstruct
    /// `common_refinement(m1, m2).0` and match it syntactically against a
    /// fixed subterm. `riemann_sum_shared_accuracy_close`'s own proof now
    /// calls this theorem's underlying construction directly
    /// (`creal/integral.rs`'s private `shared_accuracy_close_at_proof`), so
    /// the specialized and general versions share one proof, not two.
    pub riemann_sum_shared_accuracy_close_at: NameId,
    /// `CReal.riemannSumTotalEpsLe : ∀ a b e m : Nat's/CReal mix,
    /// CReal.le (totalEps a b e m) (CReal.ofRat (Rat.natDivSucc magnitude
    /// e))`, `magnitude := Nat.succ (CReal.bound (CReal.add b (CReal.neg
    /// a)))`, `totalEps` = `riemannSum_cauchy`'s own internal bound term
    /// (`creal/integral.rs`'s `total_eps_of`, reconstructed EXTERNALLY
    /// term-for-term — see that file for the exact shape).
    ///
    /// **The closed-form magnitude lemma `riemannSum_cauchy`'s own doc
    /// comment (and `riemannSum_shared_accuracy_close`'s) name as the
    /// actual remaining gate on `CReal.integral`**: `totalEps` is an opaque
    /// CReal SAMPLE until this bound turns it into a genuine
    /// `K/(e+1)`-shaped rational, independent of `m` and requiring no
    /// hypothesis on `a`/`b` at all (`CReal.bound` is unconditional; the
    /// `mul_le_mul_of_nonneg_left` step multiplies through by the
    /// UNCONDITIONALLY nonnegative `embed (natDivSucc 1 e)`, not by `width`,
    /// so `le a b` is never needed). Two independent pieces:
    ///
    /// 1. `total_eps_of a b e m` is `Equiv`-identical to `mul width (embed
    ///    (natDivSucc 1 e))` (`width := add b (neg a)`) via
    ///    `integral.rs`'s private `riemann_sum_const_rearrange` (already
    ///    proved for [`Self::riemann_sum_const`], reused at `c := embed
    ///    (natDivSucc 1 e)` — the mesh count's own cancellation identity
    ///    does not care what its "constant" factor IS) plus one `mul_comm`.
    /// 2. [`Self::mul_le_mul_of_nonneg_left`] at that nonnegative factor,
    ///    widening `width` to `direct_bound_le`'s own `ofNat magnitude`
    ///    bound, then [`Self::of_rat_mul`] plus
    ///    [`crate::RatPrelude::nat_div_succ_mul`] (`Nat.mul_one`-simplified)
    ///    collapses the resulting rational product back into a single
    ///    `natDivSucc`.
    pub riemann_sum_total_eps_le: NameId,
    /// `CReal.riemannSumDeepCauchy : ∀ F a b, CReal.le a b →
    /// CReal.UniformlyContinuousOn F a b → ∀ p q : Nat, Within (seq
    /// (riemannSum F a b (deep F a b u p)) p − seq (riemannSum F a b (deep F
    /// a b u q)) q) (bound p q)` — the Cauchy-shape statement for the
    /// RAW-indexed sequence `fun n => riemannSum F a b (deep n)`, at two
    /// INDEPENDENT accuracies `p`, `q` (`deep` computed EXACTLY the way
    /// [`Self::riemann_sum_cauchy`]'s own body computes it, extra depth `k`
    /// fixed at `0`).
    ///
    /// **The reindexing route, not the shared-accuracy one.** Unlike
    /// [`Self::riemann_sum_shared_accuracy_close`] (one accuracy `e`, two
    /// arbitrary extra depths `k1`/`k2`), this specializes
    /// [`Self::shared_index_to_canonical`]'s three free index arguments
    /// `pp := qq := jj := p` (resp. `q`) in each of its two applications —
    /// the specialization that declaration's own doc comment names as the
    /// disproved worry, made safe because those three arguments are
    /// genuinely unconstrained by the common-refinement target's own
    /// magnitude. That is what makes every leg of the resulting bound a
    /// function of `p`/`q` alone, independent of the (potentially far
    /// larger) shared refinement count — exactly the property needed to
    /// eventually reindex `riemannSum` into a literal `CReal.Cauchy`
    /// witness at rate `O(1/p) + O(1/q)`, rather than a rate governed by an
    /// unconstrained modulus. See `creal/integral.rs`'s
    /// `declare_riemann_sum_deep_cauchy` for the three-leg
    /// [`Self::regular`]/`shared_index_to_canonical`/`shared_index_to_canonical`
    /// telescope via `series::chain_within3`.
    pub riemann_sum_deep_cauchy: NameId,
    /// `CReal.riemannSumDeepCauchyFolded : ∀ F a b, CReal.le a b →
    /// CReal.UniformlyContinuousOn F a b → ∀ p q : Nat, Within (seq
    /// (riemannSum F a b (deep F a b u p)) p − seq (riemannSum F a b (deep F
    /// a b u q)) q) (Rat.natDivSucc K p + Rat.natDivSucc K q)` --
    /// [`Self::riemann_sum_deep_cauchy`]'s own three-leg `bound(p,q)` folded
    /// into the literal `Cauchy`-rate shape, `K` a `Nat` expression built
    /// purely from `magnitude := Nat.succ (CReal.bound (add b (neg a)))` --
    /// independent of `p`, `q`, `F`, `u`. This is the shape
    /// [`Self::regular_of_scaled_cauchy`] needs to build `CReal.integral`.
    /// See `creal/integral.rs`'s `declare_riemann_sum_deep_cauchy_folded`
    /// and its private `bnd_leg_plus_share_le` for the leaf accounting.
    pub riemann_sum_deep_cauchy_folded: NameId,
    /// `CReal.riemannSumDeepCauchyCross : ∀ F a b, CReal.le a b → ∀ u1 u2 :
    /// CReal.UniformlyContinuousOn F a b, ∀ n : Nat, Within (seq (riemannSum
    /// F a b (deep F a b u1 n)) n − seq (riemannSum F a b (deep F a b u2
    /// n)) n) (bound n)`.
    ///
    /// **The witness/modulus reindexing bridge**, and the resolution of
    /// this development's sharpest open question: is `CReal.integral`
    /// witness-independent? [`Self::riemann_sum_deep_cauchy`]'s own
    /// three-leg telescope is generic enough that using a DIFFERENT
    /// uniform-continuity witness for each of the two legs — rather than
    /// the same `u` for both — is the identical construction: neither
    /// [`Self::riemann_sum_cauchy`] (already `∀ u, …`), nor
    /// [`Self::shared_index_to_canonical`] (never mentions `u`), nor
    /// `integral.rs`'s private `common_refinement` (pure `Nat` arithmetic on
    /// two mesh counts, however they were built) is specific to a single
    /// witness. Specialized to ONE shared sample index `n` (`pn := qn := n`
    /// throughout), so the middle `regular` leg collapses to the trivial
    /// self-comparison `regular rsum_l n n` and no third, genuinely new,
    /// piece of mathematics is needed. See `creal/integral.rs`'s
    /// `declare_riemann_sum_deep_cauchy_cross` for the construction and
    /// [`Self::integral_witness_independent`] for what it is used to prove.
    pub riemann_sum_deep_cauchy_cross: NameId,
    /// `CReal.riemannSumDeepCauchyCrossFolded : ∀ F a b, CReal.le a b → ∀ u1
    /// u2, ∀ n : Nat, Within (seq (riemannSum F a b (deep F a b u1 n)) n −
    /// seq (riemannSum F a b (deep F a b u2 n)) n) (Rat.natDivSucc K n +
    /// Rat.natDivSucc K n)` — [`Self::riemann_sum_deep_cauchy_cross`]'s
    /// three-leg bound folded via the SAME [`Self::riemann_sum_deep_cauchy_folded`]
    /// route (`integral.rs`'s private `bnd_leg_plus_share_le`, applied twice
    /// at `idx := n`). `K` depends only on `magnitude := Nat.succ
    /// (CReal.bound (add b (neg a)))`, so it is the identical `Nat`
    /// `ExprId` [`Self::integral`]'s own construction uses (both call
    /// `integral.rs`'s private `fold_k(magnitude)`).
    pub riemann_sum_deep_cauchy_cross_folded: NameId,
    /// `CReal.riemannSumAddCauchyCross : ∀ F G a b, CReal.le a b → ∀ uFG :
    /// UniformlyContinuousOn (fun t => add (F t) (G t)) a b, ∀ uF :
    /// UniformlyContinuousOn F a b, ∀ uG : UniformlyContinuousOn G a b, ∀ n :
    /// Nat, Within (seq (riemannSum (fun t => add (F t) (G t)) a b (deep …
    /// uFG n)) n − add (seq (riemannSum F a b (deep F a b uF n)) n) (seq
    /// (riemannSum G a b (deep G a b uG n)) n)) (Rat.natDivSucc K n)`.
    ///
    /// **The three-sequence cross-bridge `integral_add` needs**: unlike
    /// [`Self::riemann_sum_deep_cauchy_cross`] (one function, two witnesses),
    /// this compares THREE Riemann sums built from three generally-different
    /// mesh counts (`F+G`'s own combo-witness mesh, `F`'s own mesh, `G`'s own
    /// mesh) at a shared sample index. `riemannSum_add`'s exact per-`m`
    /// identity only fires once all three meshes already agree, so this
    /// needs `integral.rs`'s private `common_refinement3` (three counts, not
    /// two) plus two extra `CReal.regular` self-bridges (`CReal.add` shifts
    /// its own index, so `riemannSum_add` applied at the shared mesh lands
    /// at `shift n`, not `n`) that `riemannSumDeepCauchyCross` never needed.
    /// `K` depends only on `magnitude := Nat.succ (CReal.bound (width_of a
    /// b))`. See `creal/integral.rs`'s `declare_riemann_sum_add_cauchy_cross`
    /// for the construction; already the FOLDED single-`natDivSucc` shape
    /// (no separate raw/Folded split, unlike the two-witness case).
    pub riemann_sum_add_cauchy_cross: NameId,
    /// `CReal.integral : ∀ F a b, CReal.le a b → CReal.UniformlyContinuousOn
    /// F a b → CReal := CReal.mk (speedup (diagonal f) K) (regularity
    /// proof)`, `f := fun n => riemannSum F a b (deep F a b u n)` -- built
    /// via [`Self::regular_of_scaled_cauchy`] / [`Self::mk`] on the
    /// `speedup`-reindexed diagonal of `f`, using
    /// [`Self::riemann_sum_deep_cauchy_folded`] as the `Cauchy` witness. See
    /// `creal/integral.rs`'s `declare_creal_integral` (named to avoid
    /// colliding with that file's own, unrelated, pre-existing
    /// `declare_integral`, which builds `CReal.riemannSum`).
    pub integral: NameId,
    /// `CReal.integral_converges : ∀ F a b hab u, Converges (fun n =>
    /// riemannSum F a b (Nat.add (deep F a b u n) 0)) (CReal.integral F a b
    /// hab u)`.
    ///
    /// Ties `CReal.integral`'s own `mk`/`speedup` construction back to
    /// `Converges`, fully generically in `F`/`a`/`b`/`hab`/`u` — the
    /// `f_lambda`/`K`/`cauchy_proof` triple this reconstructs is EXACTLY
    /// [`Self::integral`]'s own (`creal/integral.rs`'s `integral_witness`,
    /// shared by both declarations so they cannot drift), so
    /// [`Self::converges_of_scaled_cauchy`] applied to it produces a term
    /// whose type is `CReal.integral F a b hab u` by unfolding alone — no
    /// new estimate. See `creal/integral.rs`'s `declare_integral_converges`.
    pub integral_converges: NameId,
    /// `CReal.integral_const : ∀ c a b hab u, Equiv (CReal.integral (fun _ =>
    /// c) a b hab u) (mul c (add b (neg a)))`.
    ///
    /// The first evaluation law for `CReal.integral`: a constant function's
    /// integral is base times height. Combines [`Self::integral_converges`]
    /// (specialised at `F := fun _ => c`) with [`Self::converges_of_equiv`]
    /// (built from [`Self::riemann_sum_const`], exact for every subdivision
    /// count) via [`Self::converges_unique`] — the SAME `Nat → CReal`
    /// sequence provably converges to both `CReal.integral (fun _ => c) a b
    /// hab u` and `mul c (b−a)`, so the two are `Equiv`. See
    /// `creal/integral.rs`'s `declare_integral_const`.
    pub integral_const: NameId,
    /// `CReal.integral_witness_independent : ∀ F a b hab u1 u2, Equiv
    /// (CReal.integral F a b hab u1) (CReal.integral F a b hab u2)`.
    ///
    /// **`CReal.integral` is the integral of `F`, not "the integral computed
    /// via THIS modulus"**: choosing a different uniform-continuity witness
    /// for the same `F`/`a`/`b` produces an `Equiv`-equal value. Combines
    /// [`Self::integral_converges`] (twice, once per witness) with
    /// [`Self::converges_of_close`] fed
    /// [`Self::riemann_sum_deep_cauchy_cross_folded`] (instantiated at
    /// matching index — the cross-witness closeness bound between the two
    /// Riemann-sum diagonals) via [`Self::converges_unique`]: `f_lambda`
    /// built from `u1` provably converges to BOTH `integral … u1` (directly)
    /// and `integral … u2` (transported across the cross bound from `u2`'s
    /// own convergence), so the two integral values are `Equiv`. See
    /// `creal/integral.rs`'s `declare_integral_witness_independent`.
    pub integral_witness_independent: NameId,
    /// `CReal.integral_add : ∀ F G a b hab uFG uF uG, Equiv (CReal.integral
    /// (fun t => add (F t) (G t)) a b hab uFG) (add (CReal.integral F a b
    /// hab uF) (CReal.integral G a b hab uG))`.
    ///
    /// **The integral of a sum is the sum of the integrals.** Combines three
    /// [`Self::integral_converges`] applications with
    /// [`Self::converges_add`] and [`Self::riemann_sum_add_cauchy_cross`]
    /// (the three-sequence cross-bridge between the combo-witness's own
    /// Riemann sum and the SUM of `F`'s and `G`'s own Riemann sums, at their
    /// own generally-different mesh depths) via
    /// [`Self::converges_of_close`]/[`Self::converges_unique`] — the SAME
    /// technique [`Self::integral_witness_independent`] uses, one sequence
    /// wider. See `creal/integral.rs`'s `declare_integral_add`.
    pub integral_add: NameId,
    /// `CReal.integral_le : ∀ F G a b hab uF uG, (∀ t, le a t → le t b → le
    /// (F t) (G t)) → le (CReal.integral F a b hab uF) (CReal.integral G a b
    /// hab uG)`.
    ///
    /// **Order passes to the integral.** No `converges_unique`/`Equiv`
    /// bridge (unlike [`Self::integral_add`]/[`Self::integral_witness_independent`]):
    /// [`Self::converges_le`] takes two Converges facts at *independent*
    /// limits directly, so the obstruction is purely getting BOTH sides'
    /// native Riemann-sum sequences onto a SHARED mesh depth `l(n) :=`
    /// [`Self::riemann_sum_cauchy`]'s common refinement of `F`'s and `G`'s
    /// own `deep`-depths at `n`, at which [`Self::riemann_sum_le_on`]'s
    /// comparison is exact (no epsilon slack). One
    /// [`Self::converges_of_close`] transport per side (F's native sequence
    /// to `l(n)`, G's native sequence to `l(n)`) lands both at `l(n)`
    /// simultaneously converging to their own original limits, then
    /// `riemannSum_le_on` at `l(n)` supplies `converges_le`'s pointwise
    /// hypothesis directly. See `creal/integral.rs`'s `declare_integral_le`.
    pub integral_le: NameId,
    /// `CReal.integral_split : ∀ F a b (m_ac0 m_cb0 : Nat) (hab : le a b)
    /// (u : UniformlyContinuousOn F a b) (hac : le a c) (hcb : le c b)
    /// (uac : UniformlyContinuousOn F a c) (ucb : UniformlyContinuousOn F c b),
    /// Equiv (integral F a b hab u)
    ///       (add (integral F a c hac uac) (integral F c b hcb ucb))`,
    /// where `c := add a (mul (ofNat (succ m_ac0)) (delta_of a b (add (succ
    /// m_ac0) m_cb0)))`.
    ///
    /// **Additivity over a split interval** — the law seventeen lanes worked
    /// on. `c` is not universally quantified: it is the base split point of
    /// the caller's rational proportion `succ m_ac0 : succ m_cb0`, because
    /// [`Self::riemann_sum_split_scale_invariant`] proves `Equiv c_k c_0` for
    /// the `succ_mul_succ` mesh family and for no other, so a free `c` has
    /// nothing to be `Equiv` to. Every rational proportion is reachable
    /// (`m_ac0`/`m_cb0` are free `Nat`s); the midpoint is `m_ac0 = m_cb0`.
    ///
    /// Route — no rational estimate is done by hand at this level at all.
    /// Each of the three intervals gets a `Converges` fact at a mesh family
    /// scaled by one common factor (`integral.rs`'s `leg_converges`, over
    /// `mesh_count_align_mul_bounds`); [`Self::converges_add`] combines the
    /// two children; the split identity restated at `c`
    /// (`split_identity_at_equiv_point`, over
    /// [`Self::riemann_sum_split_exact_of_uc`] and
    /// `riemann_sum_congr_endpoints`) is APPLIED at each index, `Equiv` being
    /// exactly the per-index `Within` at `2/(n+1)`; [`Self::converges_of_close`]
    /// transports at `Kc := 2` and [`Self::converges_unique`] closes. See
    /// `creal/integral.rs`'s `declare_integral_split`.
    pub integral_split: NameId,
    /// `CReal.splitPointApprox : ∀ a b c (k : Nat), CReal.PosBound (add b
    /// (neg a)) k → CReal.le a c → CReal.le c b → ∀ (g : Nat),
    /// ∃ m_ac0 m_cb0, CReal.le (CReal.abs (add c (neg (a + (ofNat (succ
    /// m_ac0)) * ((b−a)/(succ m_ac0 + m_cb0 + 1)))))) ((4/(g+2)) * |b−a|)`
    /// — **piece 2**: an ARBITRARY `c` in `[a, b]` is approximated, to any
    /// accuracy, by a member of [`Self::integral_split`]'s own base
    /// proportion family.
    ///
    /// The `PosBound` on the width is load-bearing and is why this is not
    /// universally quantified in `c` alone: locating `c` means forming
    /// `t := (c−a)/(b−a)`, and [`Self::inv`] takes the positivity witness as
    /// an explicit argument, which `le a b` does not supply.
    ///
    /// The route bypasses [`CrossingNames::crossing_index`], [`Self::bound`] and
    /// [`Self::bucket_index_bound`] entirely — the three things five earlier
    /// lanes measured as blocking this. `t` lives in `[0,1]`, so
    /// [`Self::bucket_index`] can be read at grid `succ g` directly: the
    /// approximant `(succ m_ac0)/(g+2)` and every slack term then share ONE
    /// denominator, and the index is capped by `Nat.le_total` — `Nat` order
    /// IS decidable — rather than by `bucket_index_bound`'s `+3` slack, which
    /// is what made the rescaled-mesh route fail. See
    /// `creal/integral.rs`'s `declare_split_point_approx`.
    pub split_point_approx: NameId,
    /// `CReal.integralEndpointClose` — **endpoint continuity of the
    /// integral**, mesh-free:
    ///
    /// ```text
    /// le (abs (integral F x y hxy uxy − integral F x2 y2 hx2y2 ux2y2))
    ///    (add (mul M dw) (mul (1/(e+1)) w2b))
    /// ```
    ///
    /// under the endpoint hypotheses `|x−x2| ≤ bx`,
    /// `|(y−x)−(y2−x2)| ≤ bw ≤ dw`, `|y2−x2| ≤ w2b` and
    /// `bx + bw ≤ 1/(modulus F aa bb u e + 1)`; `M` is `bounded_on_unfold`'s
    /// own bound at `derivative.rs::mag_bound`'s recipe. No Riemann sum and
    /// no mesh count appears in the statement.
    ///
    /// Built at the `Converges` altitude, NOT against
    /// [`Self::riemann_sum_integral_close`]'s sample-level `Within`: both
    /// legs run through `integral.rs`'s own `leg_converges` at ONE shared
    /// mesh family, the mesh-uniform endpoint estimate bounds the two
    /// sequences termwise, and [`Self::converges_le`] carries it to the
    /// limits. See `creal/integral.rs`.
    pub integral_endpoint_close: NameId,
    /// `CReal.integralSplitArbitrary : ∀ F a b c (k kb : Nat),
    /// PosBound (add b (neg a)) k → ∀ (hab : le a b) (u : UniformlyContinuousOn
    /// F a b), BoundedOn F a b kb → ∀ (hac : le a c) (hcb : le c b)
    /// (uac : UniformlyContinuousOn F a c) (ucb : UniformlyContinuousOn F c b),
    /// Equiv (integral F a b hab u)
    ///       (add (integral F a c hac uac) (integral F c b hcb ucb))` —
    /// **additivity of the integral over a split at an ARBITRARY interior
    /// point**, the fact `derivative.rs`'s `hasDerivative_integral_const`
    /// names as one of the two the general Fundamental Theorem needs.
    ///
    /// The `PosBound` on the width is in the signature and cannot be dropped
    /// at this stratum: locating `c` in [`Self::integral_split`]'s base
    /// proportion family means forming `t := (c−a)/(b−a)`, and [`Self::inv`]
    /// takes the positivity witness as an explicit argument.
    /// `bounded_of_uniformly_continuous` supplies the `BoundedOn` pair for
    /// free, so that hypothesis costs a caller nothing.
    ///
    /// Three named facts and no new estimate: [`Self::integral_split`] at the
    /// approximating base split point (EXACT, contributes zero),
    /// [`Self::integral_endpoint_close`] on each leg, and
    /// [`Self::abs_add_le`]; [`Self::split_point_approx`] supplies the
    /// approximating point and [`Self::equiv_zero_of_small`] closes. See
    /// `creal/integral.rs`.
    pub integral_split_arbitrary: NameId,
    /// `CReal.integralSplitAnywhere : ∀ (F : CReal → CReal) (a b c : CReal)
    /// (hab : le a b) (u : UniformlyContinuousOn F a b) (kb : Nat),
    /// BoundedOn F a b kb → ∀ (hac : le a c) (hcb : le c b)
    /// (uac : UniformlyContinuousOn F a c)
    /// (ucb : UniformlyContinuousOn F c b),
    /// Equiv (integral F a b hab u)
    ///       (add (integral F a c hac uac) (integral F c b hcb ucb))`.
    ///
    /// [`Self::integral_split_arbitrary`] **with its `PosBound` removed** —
    /// the form the Fundamental Theorem needs, since it splits at
    /// `[a, clamp y]`, whose width is zero exactly at `y = a`.
    ///
    /// The conclusion never mentions `k`, so the hypothesis is only ever
    /// used *inside* the proof: [`Self::equiv_zero_of_small`] reduces the
    /// goal to a per-accuracy bound, [`Self::lt_cotrans`] splits `0 < δ`
    /// against the width, the positive branch feeds
    /// [`Self::pos_bound_of_lt`] (whose `Exists` is eliminable because the
    /// goal is a `Prop`) and closes outright, and the degenerate branch
    /// bounds all three integrals by `M·δ` through
    /// [`Self::integral_abs_le_of_bound`]. **`inv_index_irrelevant` is not
    /// needed** — `CReal.integral` takes no `k`. See `creal/integral.rs`.
    pub integral_split_anywhere: NameId,
    /// `CReal.hasDerivative_antiderivative : ∀ (F : CReal → CReal)
    /// (a b : CReal) (hab : le a b) (u : UniformlyContinuousOn F a b)
    /// (kb : Nat), BoundedOn F a b kb →
    /// HasDerivativeOn (antiderivative F a b hab u) F a b`.
    ///
    /// **The Fundamental Theorem of Calculus, part I** — the antiderivative
    /// of a uniformly continuous `F` on `[a, b]` has derivative `F` there.
    ///
    /// `HasDerivativeOn`'s spec quantifies over an UNORDERED pair and
    /// `CReal.le` is undecidable, so `G(y) − G(x)` cannot be written as one
    /// integral `∫ₓ^y F`. With `m := min x y` as a COMMON base point both
    /// legs are [`Self::integral_sub_linear_le`] at base `x`, and their
    /// difference is exactly `G(y) − G(x) − F(x)·(y − x)`; each leg's width
    /// is at most `max x y − min x y`, which [`Self::max_sub_min`] identifies
    /// with `|y − x|`. Modulus `λ E ↦ modulus F a b u (2E+1)`, so two halves
    /// of `1/(2E+2)` sum to the `1/(E+1)` the spec asks for.
    ///
    /// Four facts make it go through, none an estimate:
    /// [`Self::clamp_mono`] (the two splits are legal),
    /// [`Self::clamp_id`] (the raw `x`, `y` reappear in the error term),
    /// [`Self::max_sub_min`], and [`Self::integral_split_anywhere`] — the
    /// split is at `[a, clamp y]`, whose width is zero at `y = a`, so
    /// `integral_split_arbitrary`'s `PosBound` fails precisely here.
    /// See `creal/integral.rs`.
    pub has_derivative_antiderivative: NameId,
    /// `CReal.integral_eq_antideriv_diff : ∀ F G a b (hab : le a b)
    /// (u : UniformlyContinuousOn F a b) (kb : Nat), BoundedOn F a b kb →
    /// HasDerivativeOn G F a b →
    /// Equiv (integral F a b hab u) (add (G b) (neg (G a)))`.
    ///
    /// **The Fundamental Theorem of Calculus, part II — the evaluation
    /// rule**, for ANY antiderivative `G` of `F`, not just
    /// [`Self::antiderivative`] itself. `A := antiderivative F a b hab u` is
    /// ALSO an antiderivative ([`Self::has_derivative_antiderivative`],
    /// FTC-I), so `G − A` has derivative `zero`
    /// ([`Self::has_derivative_sub`] + [`Self::add_neg`]), and
    /// [`Self::constant_of_zero_deriv`] gives `G a − A a ~ G b − A b`.
    /// `A a ~ zero` and `A b ~ integral F a b hab u` are both instances of
    /// the SAME degenerate-interval fact (`[a, clamp a]` and `[clamp b, b]`
    /// respectively, via [`Self::clamp_id`] + [`Self::integral_abs_le`]);
    /// the final rearrangement `G a ~ G b − I ⟹ I ~ G b − G a` is pure
    /// `add_assoc`/`add_comm`/`add_neg`/`add_zero` algebra. See
    /// `creal/integral.rs`.
    pub integral_eq_antideriv_diff: NameId,
    /// `CReal.integral_by_parts : ∀ u u' v v' a b (hab : le a b),
    /// HasDerivativeOn u u' a b → HasDerivativeOn v v' a b →
    /// UniformlyContinuousOn u a b → UniformlyContinuousOn u' a b →
    /// UniformlyContinuousOn v a b → UniformlyContinuousOn v' a b →
    /// Equiv (integral (fun r => mul (u' r) (v r)) a b hab ‹u'v witness›)
    ///       (add (add (mul (u b) (v b)) (neg (mul (u a) (v a))))
    ///            (neg (integral (fun r => mul (u r) (v' r)) a b hab
    ///                  ‹uv' witness›)))`.
    ///
    /// **Integration by parts.** [`Self::has_derivative_mul`] gives `(uv)' =
    /// u'v + uv'` (its own explicit `UniformlyContinuousOn u` plus three
    /// magnitude-bound hypotheses, discharged here via
    /// [`Self::bounded_of_uniformly_continuous`] against the four
    /// caller-supplied `UniformlyContinuousOn` witnesses — one per `u`, `u'`,
    /// `v`, `v'` — rather than taken as independent hypotheses the way
    /// [`Self::has_derivative_cube`] does, since here they are all cheaply
    /// available). [`Self::integral_eq_antideriv_diff`] (FTC-II) applied to
    /// `u*v` gives `∫(u'v+uv') = u(b)v(b) − u(a)v(a)`; [`Self::integral_add`]
    /// splits the left side into `∫u'v + ∫uv'`; the final rearrangement `I1 +
    /// I2 ~ D ⟹ I1 ~ D − I2` reuses `integral.rs`'s own private
    /// `add_cancel_right` (already built for FTC-II's closing step). Every
    /// gap between a hand-built lambda (`u'v`, `uv'`, `u'v+uv'`, `u*v`) and
    /// the shape a combinator's own conclusion produces is a pure beta
    /// redex, bridged by the kernel's defeq check the same way
    /// [`Self::integral_eq_antideriv_diff`]'s own `h_dab` bridge works — no
    /// extra congruence lemma. See `creal/integral.rs`'s
    /// `declare_integral_by_parts`.
    pub integral_by_parts: NameId,
    /// `CReal.integral_abs_le : ∀ F a b (k : Nat) (hab : le a b)
    /// (u : UniformlyContinuousOn F a b), BoundedOn F a b k →
    /// le (abs (integral F a b hab u))
    ///    (mul (ofRat (Rat.natDivSucc (Nat.succ k) 0)) (add b (neg a)))`.
    ///
    /// **The integral is bounded by `M · (b − a)`.** No new estimate: a
    /// `BoundedOn` witness squeezes `F` between the two CONSTANT functions
    /// `±M` pointwise on `[a, b]`, [`Self::integral_le`] carries that to the
    /// integrals, and [`Self::integral_const`] evaluates both ends exactly.
    /// Nothing in the proof touches a Riemann sum, a mesh count or a modulus.
    ///
    /// `M` is `derivative.rs`'s own `mag_bound k`, the exact term
    /// [`Self::bounded_on_unfold`]'s conclusion carries — a convenient literal
    /// would not type-check.
    ///
    /// Needed by both remaining pieces of additivity at an ARBITRARY split
    /// point (it is the `M·δ` leaf of the close-endpoint estimate, and it
    /// discharges the degenerate branch of the cotransitivity split that
    /// removes the positivity hypothesis on `b − a`), and by the Fundamental
    /// Theorem directly for the antiderivative's own continuity. See
    /// `creal/integral.rs`'s `declare_integral_abs_le`.
    pub integral_abs_le: NameId,
    /// `CReal.integral_abs_le_of_bound : ∀ (F : CReal → CReal) (a b M : CReal)
    /// (hab : le a b) (u : UniformlyContinuousOn F a b),
    /// (∀ t, le a t → le t b → le (abs (F t)) M) →
    /// le (abs (integral F a b hab u)) (mul M (add b (neg a)))`.
    ///
    /// [`Self::integral_abs_le`] with its bound generalized from the
    /// `Nat`-derived `mag_bound k` (which is `k + 1`, hence never smaller
    /// than one) to an **arbitrary `CReal`**, and its `BoundedOn` witness
    /// replaced by the pointwise hypothesis that witness was only used to
    /// produce. The Fundamental Theorem needs a bound that SHRINKS
    /// (`1/(e+1)`), which no `mag_bound k` can be, so this generalization is
    /// mandatory rather than cosmetic. The proof is
    /// [`Self::integral_abs_le`]'s own, term for term
    /// ([`Self::integral_le`] + [`Self::integral_const`] against the two
    /// constant functions `±M`); no new estimate, no Riemann sum, no
    /// modulus. See `creal/integral.rs`'s `declare_integral_abs_le_of_bound`.
    pub integral_abs_le_of_bound: NameId,
    /// `CReal.integral_sub_linear_le : ∀ (F : CReal → CReal) (x y z B : CReal)
    /// (hxy : le x y) (u : UniformlyContinuousOn F x y),
    /// (∀ t, le x t → le t y → le (abs (add (F t) (neg (F z)))) B) →
    /// le (abs (add (integral F x y hxy u) (neg (mul (F z) (add y (neg x))))))
    ///    (mul B (add y (neg x)))` —
    /// **`|∫ₓ^y F − F(z)·(y − x)| ≤ B·(y − x)`**.
    ///
    /// The base point `z` is a parameter INDEPENDENT of the interval's left
    /// endpoint, because nothing in the proof uses `z = x` and the
    /// Fundamental Theorem needs exactly the case where they differ: its
    /// orientation-free decomposition reads this theorem over `[min x y, y]`
    /// and `[min x y, x]` with the base point `x` in both (see
    /// `creal/integral.rs`'s module documentation).
    ///
    /// The SECOND of the two facts
    /// [`Self::has_derivative_integral_const`] names as missing for the
    /// general Fundamental Theorem; the first is
    /// [`Self::integral_split_arbitrary`], already landed. Four named facts
    /// and no new estimate: [`Self::integral_add`] splits the integrand
    /// `t ↦ F t − F x`, [`Self::integral_const`] evaluates the constant leg
    /// EXACTLY (so no [`Self::integral_scale`] is needed — the `−F(x)` leg
    /// is a constant FUNCTION, not a scalar multiple), `integral.rs`'s own
    /// `neg_mul_left_local` moves the negation out, and
    /// [`Self::integral_abs_le_of_bound`] bounds the combined integrand. The
    /// uniform-continuity witness for `t ↦ F t − F x` is derived inside from
    /// [`Self::uniformly_continuous_sub`] against
    /// [`Self::uniformly_continuous_const`], so the caller supplies nothing
    /// beyond `u`. See `creal/integral.rs`'s
    /// `declare_integral_sub_linear_le`.
    pub integral_sub_linear_le: NameId,
    /// `CReal.antiderivative : ∀ (F : CReal → CReal) (a b : CReal), le a b →
    /// UniformlyContinuousOn F a b → CReal → CReal := fun F a b hab u x =>
    /// integral F a (max a (min x b)) _ _` — the antiderivative `G(x) :=
    /// ∫ₐˣ F` of Spivak Ch. 14, as a genuinely **total** `CReal → CReal`.
    ///
    /// `HasDerivativeOn`'s carrier must be total, but [`Self::integral`]'s
    /// second and third arguments are PROOFS that exist only for an endpoint
    /// actually in `[a, b]`. Clamping supplies both unconditionally:
    /// [`Self::le_max_left`] needs no hypothesis, and `max a (min x b) ≤ b`
    /// is [`Self::max_le`] at `hab`/[`Self::min_le_right`]. **The per-`x`
    /// uniform-continuity witness is not rebuilt per `x`**: the single `u`
    /// on `[a, b]` is restricted to `[a, clamp x]` by
    /// [`Self::uniformly_continuous_on_restrict`], modulus unchanged. See
    /// `creal/integral.rs`'s `declare_antiderivative`.
    pub antiderivative: NameId,
    /// `CReal.antiderivative_abs_le : ∀ (F : CReal → CReal) (a b M : CReal)
    /// (hab : le a b) (u : UniformlyContinuousOn F a b),
    /// (∀ t, le a t → le t b → le (abs (F t)) M) → ∀ x,
    /// le (abs (antiderivative F a b hab u x))
    ///    (mul M (add (max a (min x b)) (neg a)))` — the antiderivative's
    /// **growth bound**, `|G(x)| ≤ M·(x − a)` at the clamped `x`.
    ///
    /// [`Self::integral_abs_le_of_bound`] read at `[a, clamp x]`, with the
    /// pointwise hypothesis transported from `[a, b]` by one
    /// [`Self::le_trans`]. This is NOT the Lipschitz estimate `|G(y) − G(x)|
    /// ≤ M·|y − x|`: that needs `G(y) − G(x) ~ ∫ₓ^y F`, i.e.
    /// [`Self::integral_split_arbitrary`], whose `PosBound` on the outer
    /// width and `le` between the split points are both unavailable for the
    /// unordered pair in `HasDerivativeOn`'s spec — see `creal/integral.rs`'s
    /// module documentation for the orientation-free route that removes the
    /// ordering half. See `creal/integral.rs`'s
    /// `declare_antiderivative_abs_le`.
    pub antiderivative_abs_le: NameId,
    /// `CReal.integral_scale : ∀ c F a b hab uF ucF, Equiv (CReal.integral
    /// (fun t => mul c (F t)) a b hab ucF) (mul c (CReal.integral F a b hab
    /// uF))`.
    ///
    /// **Pulling a constant factor out of the integral.** Needs only TWO
    /// witnesses (`uF` for `F`, `ucF` for `combined := fun t => mul c (F
    /// t)`), landed on a shared mesh `l(n)` exactly [`Self::integral_le`]'s
    /// own two-witness recipe (`combined` in `G`'s slot), plus ONE exact
    /// per-`m` bridge at that shared mesh: [`Self::mul_riemann_sum`]. Unlike
    /// the obstruction this law was expected to hit (`CReal.mul`'s own
    /// index-shift depending on both operands' magnitudes), no fresh
    /// Lipschitz-style bound on `CReal.mul` is derived by hand:
    /// [`Self::converges_mul`] — already proved — is used as a BLACK BOX to
    /// transport `F`'s own shared-mesh convergence through multiplication by
    /// the constant sequence `fun _ => c` ([`Self::converges_of_const`]),
    /// and [`Self::converges_unique`] closes the gap against `combined`'s
    /// own shared-mesh convergence (bridged to the scaled sequence via
    /// `mul_riemann_sum` applied pointwise). See `creal/integral.rs`'s
    /// `declare_integral_scale`.
    pub integral_scale: NameId,
    /// `CReal.riemannSum_integral_close : ∀ F a b, le a b →
    /// UniformlyContinuousOn F a b → ∃ K, ∀ e depth i j1 j2 : Nat, Within
    /// (Rat.sub (seq (riemannSum F a b (Nat.add (deep F a b u e) depth)) i)
    /// (seq (CReal.integral F a b hab u) e)) (bnd1 + bnd2 + natDivSucc K e)`,
    /// `bnd1`/`bnd2` EXACTLY [`Self::riemann_sum_shared_accuracy_close`]'s
    /// own two-leg bound at `(e, k1 := depth, k2 := 0, oi := i, oj := e, j1,
    /// j2)`. `K` is a SINGLE rate valid for every accuracy `e` (it depends
    /// only on `F`/`a`/`b`, via [`Self::integral_converges`]'s own witness),
    /// so it sits OUTSIDE the `∀ e …` quantifiers rather than threaded
    /// through them.
    ///
    /// **The Riemann-sum-vs-true-value estimate — Chapter 14's last algebra
    /// gap.** `riemannSum F a b m` at ANY FIXED mesh count `m` at least as
    /// deep as the `e`-accuracy Archimedean threshold (`m := deep(e) +
    /// depth`, `depth` free) sits within an explicit, `e`-derived distance of
    /// `CReal.integral F a b hab u` — the standard "Riemann sums converge to
    /// the integral" statement, quantitative rather than asymptotic. Two
    /// legs, chained by `creal/integral.rs`'s own private `chain_within2`:
    ///
    /// 1. [`Self::riemann_sum_shared_accuracy_close`] at `k1 := depth`, `k2
    ///    := 0` — comparing the FIXED mesh `m` against `deep(e) + 0`, which
    ///    is EXACTLY `integral.rs`'s own private `integral_witness`'s
    ///    `f_lambda` evaluated at `e`.
    /// 2. [`Self::integral_converges`]'s own `Converges f_lambda
    ///    integral_val` fact, ELIMINATED (rather than re-derived by hand)
    ///    to bridge `f_lambda e`'s own sample at `e` to `CReal.integral F a
    ///    b hab u`'s sample at `e`.
    ///
    /// **Leg 2 was originally built by reconstructing `integral_witness`'s
    /// `(f_lambda, K, cauchy_proof)` triple and applying
    /// [`Self::speedup_close`] directly, to get `K` NAMED rather than
    /// hidden behind [`Self::integral_converges`]'s `Exists`. Measured
    /// 2026-08-27: that route cost 74s of a 75s prelude build** (isolated by
    /// disabling each leg in turn — leg 1 alone cost no more than the ~18s
    /// baseline, leg 2 alone reproduced the full cost). The mechanism: that
    /// route's `z := sample(integral_val, e)` (built from `CReal.integral`,
    /// a `Definition` whose stored value embeds a full
    /// `regular_of_scaled_cauchy` construction) had to be shown DEFEQ
    /// against a raw `speedup(raw, K) e` term that never mentions
    /// `CReal.integral` at all — bridging them forces a full delta-unfold of
    /// `CReal.integral`'s definition. The current route never triggers that
    /// unfold: leg 2's `z`-side comes from [`Self::integral_converges`]'s
    /// own eliminated witness, whose type builds `integral_val` via the
    /// IDENTICAL `d.const_app(p.integral, …)` recipe used here, so the two
    /// are the SAME `ExprId`, not merely defeq. `K` is still genuinely
    /// NAMED (bound by the elimination's own minor premise) — just
    /// re-exposed as an outer `∃ K` on this declaration's own statement
    /// instead of reconstructed from scratch. Verified back to the ~18s
    /// `creal_prelude_builds` baseline after the rebuild.
    ///
    /// No new estimate anywhere: every piece is an already-proved lemma or an
    /// already-built construction, applied at the right arguments — the same
    /// "the telescope was already there" shape
    /// [`Self::integral_witness_independent`]'s own doc comment describes.
    /// Bridging this across a partition split at `c` (`integral_split`'s own
    /// remaining gap, per `integral.rs`'s module documentation) is NOT
    /// attempted here.
    pub riemann_sum_integral_close: NameId,
    /// `CReal.riemannSum_split_exact : ∀ F a b m_ac m_cb, (∀ x y, Equiv x y ->
    /// Equiv (F x) (F y)) -> Equiv (riemannSum F a b (add (Nat.succ m_ac)
    /// m_cb)) (add (riemannSum F a c m_ac) (riemannSum F c b m_cb))`, `c :=
    /// add a (mul (ofNat (Nat.succ m_ac)) (delta_of a b (add (Nat.succ m_ac)
    /// m_cb)))` -- the ninth `integral_split` slice
    /// (`integral::declare_riemann_sum_split_exact`, `integral.rs`'s own
    /// module documentation): an EXACT (no estimate) interval split once `c`
    /// is chosen to BE a sample point of a suitably refined `[a,b]` mesh,
    /// rather than an arbitrary `CReal`. Needs no rationality of any
    /// proportion `c` sits at -- only that `c` is literally that mesh point --
    /// so it is strictly more general than the rational-split-point slice it
    /// was sized for; connecting an arbitrary rational `q` (`c := a +
    /// q*(b-a)`) to such a mesh point (choosing counts commensurate with `q`'s
    /// denominator) is the remaining assembly step, not attempted here.
    pub riemann_sum_split_exact: NameId,
    /// `CReal.riemannSum_split_scale_invariant : ∀ a b m_ac0 m_cb0 k, Equiv
    /// c_k c_0`, where `c_k`/`c_0` are
    /// [`Self::riemann_sum_split_exact`]'s own `c` formula read at the
    /// scaled counts `(succ_mul_succ(m_ac0,k).0, succ_mul_succ(m_cb0,k).0)`
    /// vs. the base counts `(m_ac0, m_cb0)` -- `integral_split`'s gap 1,
    /// the accuracy-parameterized mesh family's `c`-independence
    /// (`integral::declare_riemann_sum_split_scale_invariant`,
    /// `integral.rs`'s own module documentation). Fixing a ratio once and
    /// scaling both sub-counts by the same `Nat.succ k` leaves the split
    /// point unchanged, so `k` is free to be grown to whatever accuracy
    /// threshold [`Self::riemann_sum_integral_close`] needs on all three
    /// intervals without moving the point the family approximates. Via
    /// [`Self::mesh_reciprocal_mul`] (exact mesh scaling) and
    /// `Nat.right_distrib`/`Nat.succ_injective` (the count bookkeeping
    /// showing the scaled combined count matches
    /// `riemannSum_split_exact`'s own convention).
    pub riemann_sum_split_scale_invariant: NameId,
    /// `CReal.congrOfUniformlyContinuous : ∀ F a b, UniformlyContinuousOn F a
    /// b → ∀ x y, le a x → le x b → le a y → le y b → Equiv x y → Equiv (F
    /// x) (F y)` -- the DOMAIN-RESTRICTED half of
    /// [`Self::riemann_sum_split_exact`]'s `hcong` hypothesis, derived
    /// directly from a uniform-continuity witness
    /// (`integral::declare_congr_of_uniformly_continuous`, `integral.rs`'s
    /// own module documentation). Cannot be strengthened to the GLOBAL
    /// `hcong` shape `riemannSum_split_exact` states: `UniformlyContinuousOn`
    /// says nothing about `F` outside `[a, b]`, so a genuinely global
    /// version is false for an arbitrary witness. Via
    /// [`Self::equiv_abs_diff_le`] / [`Self::uc_spec`] /
    /// [`Self::equiv_zero_of_small`], reusing `integral.rs`'s own
    /// `pointwise_block_equiv` middle section verbatim.
    pub congr_of_uniformly_continuous: NameId,
    /// `CReal.riemannSum_split_exact_of_uc : ∀ F a b m_ac m_cb,
    /// UniformlyContinuousOn F a b → le a b → Equiv (riemannSum F a b (add
    /// (Nat.succ m_ac) m_cb)) (add (riemannSum F a c m_ac) (riemannSum F c b
    /// m_cb))`, `c` exactly as in [`Self::riemann_sum_split_exact`] — the
    /// SAME identity, discharged from a `UniformlyContinuousOn` witness
    /// instead of the (structurally unsatisfiable-in-general)
    /// `hcong`. [`Self::riemann_sum_split_exact`] itself is UNCHANGED; see
    /// `integral::declare_riemann_sum_split_exact_of_uc`'s own doc comment
    /// for the route (bounded `sumRange` congruence against
    /// [`Self::riemann_sample_in_bounds`] and
    /// [`Self::congr_of_uniformly_continuous`]).
    pub riemann_sum_split_exact_of_uc: NameId,
    /// `CReal.hasDerivative_integral_const : ∀ c a b (k : Nat), le (abs c)
    /// (ofRat (natDivSucc (Nat.succ k) 0)) → HasDerivativeOn (fun x =>
    /// integral (fun _ => c) a (max a (min x b)) (le_max_left a (min x b))
    /// (uniformly_continuous_const c a (max a (min x b)))) (fun _ => c) a
    /// b` — Spivak Ch14's FIRST evaluation instance of the Fundamental
    /// Theorem of Calculus, part I: the antiderivative of a **constant**
    /// integrand has that constant as its derivative.
    ///
    /// `HasDerivativeOn`'s carrier `G : CReal → CReal` must be a genuinely
    /// TOTAL function, but [`Self::integral`]'s own second and third
    /// arguments are PROOFS (`le a x`, `UniformlyContinuousOn F a x`) that
    /// only exist when `x` is actually in `[a, b]` — so the naive `fun x =>
    /// integral F a x hax ux` is not well-typed at all. The fix is
    /// `max a (min x b)`: it clamps ANY `x` into `[a, b]` UNCONDITIONALLY
    /// (`le_max_left` needs no hypothesis at all), and for a **constant**
    /// integrand [`Self::uniformly_continuous_const`] is *also*
    /// unconditional (`UniformlyContinuousOn (fun _ => c) p q` holds for
    /// ANY `p q`, no ordering needed) — so both proof arguments `integral`
    /// needs are constructible for every `x`, with no case split on order
    /// (which would need decidability this development does not have).
    ///
    /// This is deliberately NOT the general FTC-I (`HasDerivativeOn G F a b`
    /// for an arbitrary uniformly continuous `F`, `G := fun x => integral F
    /// a (clamp x) …`). That needs two pieces this prelude does not yet
    /// have: additivity of `integral` over a split point (`integral F a y ~
    /// integral F a x + integral F x y`) — `super::integral`'s own module
    /// documentation flags the `riemannSum` analogue as "**Not attempted**,
    /// which is false for a FIXED subinterval count" — and a genuine
    /// Riemann-sum-vs-`F(x)·(y−x)` estimate through `F`'s own modulus of
    /// uniform continuity (what makes the error term shrink at all).
    /// Neither is a missing one-line lemma; both are open analytic
    /// development. The clamp/well-typedness fix proved here is orthogonal
    /// to that gap and applies unchanged once it closes.
    ///
    /// Built from [`Self::has_derivative_id`], [`Self::has_derivative_const`]
    /// (at `c := a`), [`Self::has_derivative_sub`] and
    /// [`Self::has_derivative_smul`] (composing to `HasDerivativeOn (fun r
    /// => mul c (add r (neg a))) (fun x => mul c (add one (neg zero))) a
    /// b` via pure beta — no `Equiv` lemma needed for that composition, only
    /// for the final cleanup), then [`Self::has_derivative_congr`] ONCE at
    /// the end to reach the stated `G`/`(fun _ => c)` on both sides: `G x ~
    /// mul c (add x (neg a))` on `[a,b]` chains [`Self::integral_const`]
    /// (global, any `x`) with `max a (min x b) ~ x` on `[a,b]`
    /// (`equiv_of_le_le` antisymmetry from `min`/`max`'s universal
    /// properties, needing `le a x`/`le x b`); `c ~ mul c (add one (neg
    /// zero))` is `mul_one`/`add_zero`/`add_neg` and does not need the
    /// interval hypotheses at all.
    ///
    /// `hasDerivative_smul`'s own magnitude-bound hypothesis (`k`, `hbound`)
    /// is left universally quantified rather than derived from
    /// [`Self::archimedean`] — the `hasDerivative_cube`/`hasDerivative_pow`
    /// pattern of pushing a Skolem witness onto the caller rather than
    /// solving the `ofNat`-vs-`natDivSucc` conversion inline.
    pub has_derivative_integral_const: NameId,
    /// `CReal.neg_sub_swap : ∀ a b, Equiv (neg (add a (neg b))) (add b (neg
    /// a))` (`creal/order_extra.rs`) — negating a difference reverses it.
    /// Added for `creal/uniform_convergence.rs` (Spivak Ch24); see that
    /// file's module documentation and `order_extra.rs`'s own section
    /// comment for why this specific compound identity, rather than a
    /// `neg_add`/`neg_neg` pair, is what got proved.
    pub neg_sub_swap: NameId,
    /// `CReal.abs_le_of_two_sided : ∀ x y q : Rat, le x (add y (ofRat q)) →
    /// le y (add x (ofRat q)) → le (abs (add x (neg y))) (ofRat q)`
    /// (`creal/order_extra.rs`) — the converse of
    /// [`Self::two_sided_of_abs_sub_le`]: rebuilds a `close_within`-shaped
    /// bound from the two "shifted" one-sided `le` facts a triangle-of-three
    /// argument naturally produces.
    pub abs_le_of_two_sided: NameId,
    /// `CReal.UniformConvergesOn (F : Nat → CReal → CReal) (G : CReal →
    /// CReal) (a b : CReal) : Type := mk (rate : Nat) (spec : …)`
    /// (`creal/uniform_convergence.rs`, Spivak Ch24) — uniform convergence of
    /// a sequence of functions on `[a, b]`. See that file's module
    /// documentation for why `rate` is a genuine `Nat` DATA field (mirroring
    /// [`Self::uniformly_continuous_on`]'s own `Type`-valued shape) rather
    /// than an `Exists`-wrapped `Prop`.
    pub uniform_converges_on: NameId,
    /// `UniformConvergesOn.mk`, the one constructor.
    pub uconv_mk: NameId,
    /// `UniformConvergesOn.rec`, the kernel-generated recursor (four leading
    /// parameters `F G a b`).
    pub uconv_rec: NameId,
    /// `UniformConvergesOn.rate : ∀ F G a b, UniformConvergesOn F G a b →
    /// Nat` — the data field, by large elimination.
    pub uconv_rate: NameId,
    /// `UniformConvergesOn.spec` — the `Prop`-valued field, projected with
    /// the motive at a witness `u` mentioning `u`'s own `rate`.
    pub uconv_spec: NameId,
    /// `CReal.uniform_converges_id : ∀ a b, UniformConvergesOn (fun n x =>
    /// x) (fun x => x) a b` — `F n x := x` (constant in `n`) converges
    /// uniformly to `id`, at `rate := 1`.
    pub uniform_converges_id: NameId,
    /// `CReal.uniform_converges_geom_half : UniformConvergesOn (fun n x =>
    /// mul x (pow half n)) (fun _ => zero) zero one` — `F n x := x·(1/2)^n`
    /// converges uniformly to the constant `0` on `[0, 1]`, at `rate := 1`.
    pub uniform_converges_geom_half: NameId,
    /// `CReal.uniform_limit_uniformly_continuous : ∀ F G a b,
    /// UniformConvergesOn F G a b → (∀ n, UniformlyContinuousOn (F n) a b) →
    /// UniformlyContinuousOn G a b` (`creal/uniform_convergence.rs`, Spivak
    /// Ch24's headline theorem) — the uniform limit of uniformly continuous
    /// functions is uniformly continuous.
    pub uniform_limit_uniformly_continuous: NameId,

    // --- polynomials over `CReal` (creal/polynomial.rs) ----------------------
    /// `creal/polynomial.rs`'s own 10 names, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.polynomial.poly_eval` and documented in
    /// [`PolynomialNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub polynomial: PolynomialNames,
    /// `CReal.uniform_converges_add : ∀ F H G K a b, UniformConvergesOn F G a
    /// b → UniformConvergesOn H K a b → UniformConvergesOn (fun n x => add (F
    /// n x) (H n x)) (fun x => add (G x) (K x)) a b`
    /// (`creal/uniform_convergence.rs`) — sums preserve uniform convergence:
    /// the pointwise-sum rate is the SUM of the two rates (`k1 + k2`),
    /// exactly, via `Rat.natDivSucc_add` fusing the two per-index bounds.
    /// Uses [`Self::two_sided_of_abs_sub_le`]/[`Self::abs_le_of_two_sided`] to
    /// split and recombine each `close_within` fact, exactly as
    /// [`Self::uniform_limit_uniformly_continuous`] does, but skips that
    /// theorem's private `weaken_rate` index-widening step entirely: both
    /// bounds already share the SAME denominator index `n`, so no scaling
    /// across different function indices is needed, only a rearrangement of
    /// the sum.
    pub uniform_converges_add: NameId,
    /// `CReal.close_within_of_within : ∀ x y n k, Within (Rat.sub (seq x n)
    /// (seq y n)) (natDivSucc k n) → le (abs (add x (neg y))) (ofRat
    /// (natDivSucc (1+(k+1)) n))` (`creal/uniform_convergence.rs`) — the
    /// `Within → close_within` bridge, generic in BOTH `x` and `y`: a raw
    /// rational sample-level bound at a SHARED index `n` lifts to a genuine
    /// real-valued closeness fact, via each side's own `1/(n+1)`-slack
    /// self-approximation ([`Self::sample_upper_bound`]/
    /// [`Self::sample_lower_bound`]) rather than `CReal.regular` read at a
    /// shifted index. `Converges`/`Cauchy` (`creal/convergence.rs`) state
    /// everything in `Within` form; this is what a caller building a
    /// `CReal.UniformConvergesOn` instance from such an estimate (e.g. the
    /// Weierstrass M-test) needs to reach `close_within`.
    pub close_within_of_within: NameId,
    /// `CReal.close_within_of_within_indexed : ∀ x y i e q, Within (Rat.sub
    /// (seq x i) (seq y e)) q → le (abs (add x (neg y))) (ofRat (Rat.add q
    /// (Rat.add (natDivSucc 1 i) (natDivSucc 1 e))))` (`creal/integral.rs`)
    /// — the two-INDEPENDENT-index generalization of
    /// [`Self::close_within_of_within`]: that lemma needs `x` and `y`
    /// sampled at the SAME index `n`, but `riemannSum_integral_close`'s own
    /// `Within` fact compares `riemannSum`'s sample at an arbitrary `i`
    /// against `integral`'s sample at the accuracy index `e` — two indices
    /// never tied by a common denominator anywhere upstream. Same route
    /// (each side's own `1/(index+1)`-slack self-approximation via
    /// [`Self::sample_upper_bound`]/[`Self::sample_lower_bound`], read at
    /// its OWN index), run once per direction with `(i, e)` swapped, then
    /// unified onto one shared bound via `Rat.add_assoc`/`Rat.add_comm`
    /// (the two directions' raw bounds differ only in associativity/
    /// commutativity, never syntactically).
    pub close_within_of_within_indexed: NameId,
    /// `CReal.weierstrassMTest : ∀ (f : Nat → CReal → CReal) (mseq : Nat →
    /// CReal) (a b : CReal), le a b → (∀ j p q, Equiv p q → Equiv (f j p) (f
    /// j q)) → ∀ k, (∀ j pt, le a pt → le pt b → le (abs (f j pt)) (mseq
    /// j)) → (∀ pp qq, Within (seq (sumRange mseq pp) pp − seq (sumRange
    /// mseq qq) qq) (natDivSucc k pp + natDivSucc k qq)) →
    /// UniformConvergesOn (fun n pt => sumRange (fun j => f j pt) n) (fun pt
    /// => …the limit built at `clamp a b pt`…) a b` — the Weierstrass M-test
    /// (`creal/uniform_convergence.rs`). Two hypotheses beyond a first
    /// reading of the textbook statement: `le a b` and pointwise congruence
    /// of `f`, both needed so `G` can be built as a TOTAL `CReal → CReal` by
    /// clamping into `[a, b]` before invoking the domination hypothesis —
    /// see that declaration's own module documentation for why `G` cannot
    /// be built from an unconstrained point directly, and why the
    /// congruence hypothesis is not optional once it can't.
    pub weierstrass_m_test: NameId,
    /// `CReal.powerSeriesTerm : (Nat → CReal) → Nat → CReal → CReal :=
    /// fun c j x => mul (c j) (pow x j)` — the `j`-th term of the power
    /// series with coefficients `c`, evaluated at `x`. A bare `Definition`,
    /// asserting nothing. See `creal/power.rs`.
    pub power_series_term: NameId,
    /// `CReal.powerSeriesTerm_congr : ∀ c j p q, Equiv p q → Equiv
    /// (powerSeriesTerm c j p) (powerSeriesTerm c j q)` — the fact that
    /// unlocks feeding `powerSeriesTerm c` to [`Self::weierstrass_m_test`]
    /// as its own `f`: that theorem's `f` must respect `Equiv` (`CReal` is
    /// a Bishop SETOID, not a literal quotient — ADR-0512). From
    /// [`Self::pow_congr`]/[`Self::mul_congr`] directly. See
    /// `creal/power.rs`.
    pub power_series_term_congr: NameId,
    /// `CReal.powerSeriesTerm_abs_le : ∀ c M, (∀ j, le (abs (c j)) M) → ∀ x
    /// r, le zero x → le x r → ∀ j, le (abs (powerSeriesTerm c j x)) (mul M
    /// (pow r j))` — the domination package: a coefficient sequence bounded
    /// by `M` gives, for every `x` in `[0, r]`, `|c_j·x^j| ≤ M·r^j`. From
    /// [`Self::pow_le_pow_of_base_le`] (base monotonicity, `x ≤ r ⟹ x^j ≤
    /// r^j`), [`Self::pow_nonneg`] (so `abs (pow x j) ~ pow x j` doesn't
    /// need a separate `abs_of_nonneg` — the two-sided `abs_le` route mirrors
    /// `creal/monotone.rs`'s own private `abs_le_of_nonneg_le`, reproduced
    /// here since that helper is not `pub(super)`) and
    /// [`Self::abs_mul_le_of_bounds`]. See `creal/power.rs`.
    pub power_series_term_abs_le: NameId,
    /// `CReal.powerSeriesUniformConvergesOn : ∀ c M, (∀ j, le (abs (c j))
    /// M) → ∀ r, le zero r → ∀ k, (∀ pp qq, Within (seq (sumRange mseq pp)
    /// pp − seq (sumRange mseq qq) qq) (natDivSucc k pp + natDivSucc k qq))
    /// → UniformConvergesOn (fun n x => sumRange (fun j => powerSeriesTerm c
    /// j x) n) G zero r`, where `mseq j := mul M (pow r j)` — the
    /// Weierstrass M-test ([`Self::weierstrass_m_test`]) specialized to a
    /// bounded-coefficient power series on `[0, r]`: `f`'s congruence comes
    /// from [`Self::power_series_term_congr`] and the domination hypothesis
    /// from [`Self::power_series_term_abs_le`], both derived internally
    /// rather than taken as parameters. The raw Cauchy modulus `(k, …)` for
    /// the DOMINATING geometric series `M·rʲ` is still a parameter, exactly
    /// as `weierstrassMTest` itself takes one — a caller obtains it from
    /// [`RatioTestNames::geom_scaled_cauchy_of_lt`] plus an `Exists`-elimination of
    /// their own, which this declaration cannot perform internally: the
    /// M-test's own limit `G` is built FROM `k`, so a target that must not
    /// mention the witness (`Exists.rec`'s own restriction) cannot be `G`
    /// itself. `r < 1` is deliberately NOT a hypothesis here — nothing in
    /// this construction needs it; it is implicit in whatever Cauchy
    /// witness a caller can actually produce for `mseq`. See
    /// `creal/uniform_convergence.rs`.
    pub power_series_uniform_converges: NameId,
    /// `CReal.sinTerm : Nat → CReal := fun k => mul (pow (neg one) k)
    /// (expTerm (Nat.add (Nat.add k k) 1))` — the `k`-th term of `sin 1`'s
    /// Taylor series, `(-1)^k/(2k+1)!`, the odd index written `Nat.add
    /// (Nat.add k k) 1` (symbolic left, literal right) so it reduces
    /// definitionally to `Nat.succ (Nat.add k k)` — mirrors `CReal.cosTerm`
    /// exactly except for the odd index. See `creal/trig.rs`.
    pub sin_term: NameId,
    /// `CReal.sinSeriesPartial : Nat → CReal := CReal.sumRange CReal.sinTerm`
    /// — the `k`-th partial sum `Σ_{n<k} (-1)^n/(2n+1)!`. See
    /// `creal/trig.rs`.
    pub sin_series_partial: NameId,
    /// `CReal.sinTermAbsLeDominant : ∀ k, le (abs (sinTerm k)) (expDominant
    /// k)` — the [`Self::cos_term_abs_le_dominant`] analogue for the odd
    /// index, closing the descent from `expDominant (add (add k k) 1)` down
    /// to `expDominant k` via one extra [`Self::pow_le_pow_of_le_one`] step
    /// (`expDominant`'s exponent is already `succ`-headed once the odd
    /// index's own `Nat.add` ι-reduces) composed with the SAME
    /// `expDominant (add k k) ≤ expDominant k` descent `CReal.cosTerm`'s own
    /// bound already needed. See `creal/trig.rs::exp_dominant_odd_le`.
    pub sin_term_abs_le_dominant: NameId,
    /// `CReal.sinOne := CReal.mk (speedup (diagonal sinSeriesPartial) K) (…)`
    /// — `sin 1`, built via `CReal.mk` on an explicit regular sequence
    /// exactly as `CReal.cosOne`/`CReal.e` are (never by
    /// `Exists`-elimination). Reuses `CReal.e`'s own concrete Cauchy witness
    /// for `Cauchy (sumRange expDominant)` unchanged — `sinOne`'s domination
    /// series **is** `expDominant`, not a new one. See `creal/trig.rs`.
    pub sin_one: NameId,
    /// `CReal.sinOneConverges : Converges sinSeriesPartial sinOne` — the
    /// `cosOneConverges` analogue, built generically over a BOUND `(k, h)`
    /// rather than the concrete `k_final` for the same stack-overflow reason
    /// `cosOneConverges`/`e_converges` are. See `creal/trig.rs`.
    pub sin_one_converges: NameId,
    /// `CReal.sinOne_alternating_lower : ∀ m, le (sumRange sinTerm (add m
    /// m)) sinOne` — [`Self::alternating_lower_bound`] instantiated at
    /// `sinTerm`'s magnitude sequence `b j := expTerm (add (add j j) 1)`,
    /// the [`Self::cos_one_alternating_lower`] analogue. See
    /// `creal/trig.rs`.
    pub sin_one_alternating_lower: NameId,
    /// `CReal.sinOne_alternating_upper : ∀ m, le sinOne (sumRange sinTerm
    /// (succ (add m m)))` — the mirror of
    /// [`Self::sin_one_alternating_lower`], off
    /// [`Self::alternating_upper_bound`]. See `creal/trig.rs`.
    pub sin_one_alternating_upper: NameId,
    /// `CReal.sinOne_nonneg : le zero sinOne` —
    /// [`Self::sin_one_alternating_lower`] at `m := 0`: `sumRange sinTerm
    /// (add 0 0)` is ι-defeq to `zero`, so the general bracket specializes
    /// to the sign bound for free, exactly as [`Self::cos_one_nonneg`] does.
    /// See `creal/trig.rs`.
    pub sin_one_nonneg: NameId,
    /// `CReal.sinOne_le_exp_term_one : le sinOne (expTerm 1)` —
    /// [`Self::sin_one_alternating_upper`] at `m := 0`, folded through
    /// `add_comm`/`add_zero`/`mul_comm`/`mul_one` via `le_congr`, mirroring
    /// [`Self::cos_one_le_exp_term_zero`] exactly except that `sinTerm 0`
    /// reduces to `mul one (expTerm 1)` (odd index `1`, not `0`). `expTerm
    /// 1` is mathematically `1` (`1/1! = 1`) but is not reduced to the
    /// literal `CReal.one` here, for the same `Rat.normalize`/`Nat.gcd`
    /// reason [`Self::cos_one_le_exp_term_zero`]'s doc names. See
    /// `creal/trig.rs`.
    pub sin_one_le_exp_term_one: NameId,
    /// `CReal.expTerm_zero_eq_one : Eq CReal (expTerm 0) CReal.one` — the
    /// literal-`CReal.one` reduction [`Self::cos_one_le_exp_term_zero`]'s own
    /// doc names as out of scope: `Rat.normalize (ofNat 1) (factorial 0) _`
    /// does NOT hold `Eq.refl`-equal to `Rat.one`, since `Nat.gcd` does not
    /// unfold by ι even on literals. Solved WITHOUT touching `Nat.gcd` at
    /// all: `Rat.self_normalize` at `q := Rat.one` already proves `Eq Rat
    /// (normalize (ofNat 1) 1 _) Rat.one` up to two free ι-reductions
    /// (`num`/`den` of a `Rat.mk`-built value) and definitional PROOF
    /// IRRELEVANCE on the positivity argument (a `Prop`), then lifted
    /// through `CReal.ofRat`'s ordinary function congruence. See
    /// `creal/trig.rs::exp_term_lit_eq_one`.
    pub exp_term_zero_eq_one: NameId,
    /// `CReal.expTerm_one_eq_one : Eq CReal (expTerm 1) CReal.one` — the
    /// SAME route as [`Self::exp_term_zero_eq_one`] (`factorial 1` also
    /// reduces to `1` by ι alone, one more step: `Nat.mul 1 (factorial 0)`
    /// with its right argument a literal), reused unchanged for
    /// `sinOne_le_exp_term_one`'s own `expTerm 1`.
    pub exp_term_one_eq_one: NameId,
    /// `CReal.mulPowCongr : ∀ (c : Nat → CReal) (j : Nat) (x y : CReal),
    /// Equiv x y → Equiv (mul (c j) (pow x j)) (mul (c j) (pow y j))` — the
    /// power-series term congruence, built by `creal/congruence.rs`'s setoid
    /// congruence deriver by composing `mul_congr`/`pow_congr` structurally
    /// rather than by hand. See that module's own doc comment for the
    /// deriver this permanent registration exercises.
    pub mul_pow_congr: NameId,

    // --- the Extreme Value Theorem's boundary certificate (ADR-0603 row 2) ---
    /// `creal/extreme_value.rs`'s own 3 names, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.extreme_value.evt_linear` and documented in
    /// [`ExtremeValueNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub extreme_value: ExtremeValueNames,

    /// **The Intermediate Value Theorem's boundary certificate** (ADR-0603
    /// row 2) -- `creal/ivt_boundary.rs`'s own seven names, the first module
    /// registry moved out of this struct by ADR-1512.
    ///
    /// Reached as `p.ivt_boundary.ivt_plateau`, and documented in
    /// [`IvtBoundaryNames`] rather than here, so that adding a declaration to
    /// that module touches that module alone. Nothing outside it reads these
    /// names, which is what made the move local
    /// (`scripts/creal-declare-deps.py`).
    pub ivt_boundary: IvtBoundaryNames,

    // --- the least-upper-bound property's boundary certificate (ADR-0603 row 2)
    /// `creal/lub_boundary.rs`'s own 4 names, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.lub_boundary.lub_set` and documented in
    /// [`LubBoundaryNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub lub_boundary: LubBoundaryNames,

    // --- general `cos : CReal → CReal` (creal/trig_fn.rs) ---------------------
    /// `CReal.cosFnTerm : Nat → CReal → CReal := fun k x => mul (cosTerm k)
    /// (pow x (Nat.add k k))` — the `k`-th power-series term of general
    /// cosine at the point `x`, `cosTerm k` reused unchanged (so `x := one`
    /// makes this ι/δ-reduce to `cosTerm k` itself, up to `mul _ one ~ _`).
    /// See `creal/trig_fn.rs`.
    pub cos_fn_term: NameId,
    /// `CReal.cosFnTermAbsLe : ∀ x, le zero x → le x one → ∀ k, le (abs
    /// (cosFnTerm k x)) (expDominant k)` — the domination bound
    /// [`Self::weierstrass_m_test`] needs, closed WITHOUT any new
    /// domination series: `0 ≤ x ≤ 1` gives `pow x (Nat.add k k) ≤ one`
    /// ([`Self::pow_le_one`]), `abs_mul_le_of_bounds` folds that against
    /// `le_refl (abs (cosTerm k))` to `abs (cosFnTerm k x) ≤ abs (cosTerm k)`
    /// (up to `mul_one`), and [`Self::cos_term_abs_le_dominant`] closes the
    /// rest by `le_trans`. See `creal/trig_fn.rs`.
    pub cos_fn_term_abs_le: NameId,
    /// `CReal.cosFnTerm_congr : ∀ k x y, Equiv x y → Equiv (cosFnTerm k x)
    /// (cosFnTerm k y)` — [`Self::mul_pow_congr`] applied at the constant
    /// coefficient function `fun _ => cosTerm k` and exponent `Nat.add k k`.
    /// See `creal/trig_fn.rs`.
    pub cos_fn_term_congr: NameId,
    /// `CReal.cosFn : CReal → CReal` — general cosine on the bounded domain
    /// `[0, 1]`, the `G` [`Self::weierstrass_m_test`]'s own proof builds when
    /// applied at `f := cosFnTerm`, `mseq := expDominant`, `a := zero`, `b :=
    /// one`, extracted from that application's INFERRED type (never
    /// hand-reconstructed) so it is the identical closed term
    /// [`Self::cos_fn_uniform_converges`]'s own `G` slot names. See
    /// `creal/trig_fn.rs`.
    pub cos_fn: NameId,
    /// `CReal.cosFnUniformConverges : UniformConvergesOn (fun n x => sumRange
    /// (fun k => cosFnTerm k x) n) cosFn zero one` — the M-test applied at
    /// cosine's own series, ascribed against the NAMED `cosFn` (rather than
    /// the raw extracted `G`) so a caller sees the constant, not its
    /// unfolding. `expDominantCauchy`'s own concrete witness
    /// (`exp_dominant_cauchy_body_concrete`, reused unchanged from `cosOne`'s
    /// own construction) supplies the M-test's `(k, hcauchy)` pair DIRECTLY —
    /// no bridge needed. See `creal/trig_fn.rs`.
    pub cos_fn_uniform_converges: NameId,
    /// `CReal.cosFnTermAbsLeWide : ∀ x, le zero x → ∀ R, le x R → ∀ k, le
    /// (abs (cosFnTerm k x)) (mul (expDominant (Nat.add k k)) (pow R
    /// (Nat.add k k)))` — the pointwise domination bound for a domain past
    /// `[0, 1]`, ANY `R`, via [`Self::exp_term_abs_le_dominant`] at the
    /// DOUBLED index (the pre-collapse bound `cos_term_abs_le_dominant`'s
    /// own proof computes internally, one step before its final collapse
    /// to `expDominant k`) plus [`Self::pow_le_pow_of_base_le`] (base
    /// monotonicity). Deliberately NOT reduced to the literal ratio
    /// `16/25` — that needs `pow a n * pow b n ≈ pow (mul a b) n`, an
    /// identity this kernel does not have. See `creal/trig_fn.rs`'s own
    /// "2026-08-27 update" module documentation section for exactly what
    /// this piece does and does not close toward a wider `cosFn`.
    pub cos_fn_term_abs_le_wide: NameId,
    /// `CReal.cosDominant16Over25 : Nat → CReal := fun k => mul two (pow
    /// (ofRat (natDivSucc 16 24)) k)` — the dominating series for `cosFnTerm`
    /// at ratio `16/25 = (4/5)²`, `R := 8/5` (clears cosine's first zero,
    /// `≈ 1.5708`). See `creal/geometric.rs::ratio_16_over_25_witnesses`
    /// for the ratio's derivation and `creal/trig_fn.rs`.
    pub cos_dominant_16_over_25: NameId,
    /// `CReal.cosDominant16Over25CauchyBody : sum_range_cauchy_body
    /// (sumRange cosDominant16Over25) K` for a concrete `K` — the raw,
    /// non-existential Cauchy witness `CReal.weierstrassMTest`'s `hcauchy`
    /// parameter needs, at ratio `16/25` rather than `1/2`. Built via
    /// `exponential.rs`/`trig.rs`'s own `mul_deshift`/
    /// `mul_ordered_half_body`/`promote_ordered_half_to_full`/
    /// `cauchy_body_transport` (widened to `pub(super)`, unchanged
    /// otherwise) against [`Self::geom_cauchy_ordered_16_over_25`] as the
    /// base series' own ordered-half witness. See `creal/trig_fn.rs`.
    pub cos_dominant_16_over_25_cauchy_body: NameId,
    /// `CReal.powMulDistrib : ∀ a b (n : Nat), Equiv (mul (pow a n) (pow b
    /// n)) (pow (mul a b) n)` — power distributes over a product of bases
    /// at a fixed exponent, general in `a`, `b`, `n`. This is the identity
    /// `creal/trig_fn.rs`'s own "2026-08-27 update" module documentation
    /// names as missing ("no power distributes over a product"); it is
    /// declared HERE (not `power.rs`, which this task's scope leaves
    /// untouched) but proved exactly where a reader would look for
    /// `pow`-family lemmas conceptually, by an induction on `n` mirroring
    /// [`Self::pow_add`]'s own shape. See `creal/trig_fn.rs`.
    pub pow_mul_distrib: NameId,
    /// `CReal.cosFnWide : CReal → CReal` — `cosFn` extended to the domain
    /// `[0, 8/5]` (`8/5` clears cosine's first zero, `≈ 1.5708`), by
    /// [`Self::weierstrass_m_test`] applied at `f := cosFnTerm`, `mseq :=
    /// cosDominant16Over25`, `a := zero`, `b := ofRat (natDivSucc 8 4)`,
    /// bridging [`Self::cos_fn_term_abs_le_wide`]'s domination bound to
    /// [`Self::cos_dominant_16_over_25`]'s dominating series via
    /// [`Self::pow_mul_distrib`] plus a concrete `Rat` identity `(1/2 ·
    /// 8/5)² = 16/25`. A SEPARATE declaration from [`Self::cos_fn`]
    /// (`[0, 1]`), not a widening of it — existing `[0, 1]` callers are
    /// untouched. See `creal/trig_fn.rs`.
    pub cos_fn_wide: NameId,
    /// `CReal.cosFnWideUniformConverges : UniformConvergesOn (fun n x =>
    /// sumRange (fun k => cosFnTerm k x) n) cosFnWide zero (ofRat
    /// (natDivSucc 8 4))` — the M-test applied at cosine's series on the
    /// wider domain, ascribed against the named `cosFnWide`. See
    /// `creal/trig_fn.rs`.
    pub cos_fn_wide_uniform_converges: NameId,
    /// `CReal.cosFn_one_equiv_cosOne : Equiv (cosFn one) cosOne` — the
    /// `expFn_one_equiv_e` analogue for cosine: the bridge between the
    /// general power-series `cosFn` (bounded to `[0, 1]`) and the concrete
    /// `CReal.cosOne` construction, at the shared endpoint `x := 1`.
    /// Eliminates `CReal.cosOneConverges`'s `Exists` witness into a per-`n`
    /// `Within` fact, bridges it to `close_within` via
    /// `CReal.close_within_of_within`'s own per-index construction (leg 1),
    /// transports `cosFnUniformConverges`'s `.spec` at `x := one` from
    /// `cosFnTerm j one` to `cosTerm j` via `CReal.sumRange_congr` (leg 2;
    /// unlike `expFn_one_equiv_e`, this goes through `cosFnTerm` directly
    /// rather than the generic `CReal.powerSeriesTerm`, since cosine's
    /// coefficients are even-index-only — see `creal/trig_fn.rs`'s own
    /// module documentation), combines both legs by the triangle
    /// inequality, and closes with `CReal.equiv_zero_of_rate`. See
    /// `creal/trig_fn.rs`.
    pub cos_fn_one_equiv_cos_one: NameId,
    /// `CReal.cosFnWideUniformlyContinuous : UniformlyContinuousOn cosFnWide
    /// zero (ofRat (natDivSucc 8 4))` — `CReal.uniform_limit_uniformly_continuous`
    /// applied at `CReal.cosFnWideUniformConverges`, whose second hypothesis
    /// (`∀ n, UniformlyContinuousOn (F n) zero R`) is built by induction on
    /// `n` over `sumRange`'s own `add`/`zero` recursion, each term's own
    /// uniform continuity coming from a nested induction on `pow`'s base at
    /// symbolic exponent `Nat.add k k`, combined with the constant `cosTerm
    /// k` via `CReal.uniformly_continuous_mul` (`BoundedOn` hypotheses from
    /// `CReal.bounded_of_uniformly_continuous`, never hand-derived). See
    /// `creal/trig_fn.rs`.
    pub cos_fn_wide_uniformly_continuous: NameId,
    /// `CReal.cosFnWide_one_equiv_cosOne : Equiv (cosFnWide one) cosOne` —
    /// the WIDE cosine function evaluated at `1` is `creal/trig.rs`'s single
    /// constant `cosOne`. Same body as [`Self::cos_fn_one_equiv_cos_one`]
    /// (`creal/trig_fn.rs::cos_limit_at_one_equiv_cos_one`, factored out for
    /// exactly this), differing only in the two range hypotheses: `[0, 8/5]`
    /// needs `le one R` where `[0, 1]` needed `le_refl one`.
    ///
    /// **Not implied by [`Self::cos_fn_one_equiv_cos_one`].** `cosFn` and
    /// `cosFnWide` are separate `weierstrassMTest` limits on separate
    /// intervals (`creal/trig_fn.rs`'s module doc says so explicitly), and
    /// nothing in this development relates two uniform limits pointwise
    /// without an argument like this one. See `creal/trig_fn.rs`.
    pub cos_fn_wide_one_equiv_cos_one: NameId,
    /// `CReal.cosFnWide_one_nonneg : le zero (cosFnWide one)` — `cos 1 ≥ 0`
    /// for the wide cosine FUNCTION, [`Self::cos_one_nonneg`] transported
    /// across [`Self::cos_fn_wide_one_equiv_cos_one`] by `le_congr`.
    ///
    /// This is the first of the three numeric obligations a π-via-
    /// `CReal.ivt_exact_root` construction carries (the left endpoint of
    /// `[1, 8/5]`). The other two — `cos (8/5) < 0`, and a uniform positive
    /// lower bound on `sinFn` over `[1, 8/5]` — are **not** proved anywhere
    /// in this tree; `docs/plan/status/169-pi.md` sizes both. Nothing here
    /// constructs `CReal.pi` or asserts that a root exists. See
    /// `creal/trig_fn.rs`.
    pub cos_fn_wide_one_nonneg: NameId,
    /// `CReal.hasDerivativeOn_restrict : ∀ F F' a b a' b',
    /// HasDerivativeOn F F' a b → le a a' → le a' b' → le b' b →
    /// HasDerivativeOn F F' a' b'` — the sub-interval restriction of a
    /// DERIVATIVE witness, exactly
    /// [`Self::uniformly_continuous_on_restrict`]'s construction one
    /// parameter over: `HasDerivativeOn`'s `spec` takes the same four range
    /// hypotheses, so `a ≤ a' ≤ x` and `y ≤ b' ≤ b` compose through
    /// [`Self::le_trans`] and the original `spec` is reused at every
    /// `(e, x, y)` with the `modulus` field carried over unchanged.
    ///
    /// **Belongs in `creal/derivative.rs`**; declared from
    /// `creal/trig_fn.rs` only because that file is another lane's — the same
    /// parking [`Self::nat_div_succ_step_le`] already documents. General in
    /// `F`, `F'` and both interval pairs, not tied to cosine.
    pub has_derivative_on_restrict: NameId,

    // --- general `sin : CReal → CReal` (creal/trig_fn.rs) ---------------------
    /// `CReal.sinFnTerm : Nat → CReal → CReal := fun k x => mul (sinTerm k)
    /// (pow x (Nat.add (Nat.add k k) 1))` — the `k`-th power-series term of
    /// general sine at the point `x`, mirroring [`Self::cos_fn_term`] with
    /// the ODD exponent `2k+1` `sinTerm`'s own definition already uses
    /// (`creal/trig.rs::declare_sin_term`). See `creal/trig_fn.rs`.
    pub sin_fn_term: NameId,
    /// `CReal.sinFnTerm_congr : ∀ k x y, Equiv x y → Equiv (sinFnTerm k x)
    /// (sinFnTerm k y)` — [`Self::mul_pow_congr`] applied at the constant
    /// coefficient function `fun _ => sinTerm k` and exponent `Nat.add
    /// (Nat.add k k) 1`, mirroring [`Self::cos_fn_term_congr`]. See
    /// `creal/trig_fn.rs`.
    pub sin_fn_term_congr: NameId,
    /// `CReal.sinFnTermAbsLeWide : ∀ x, le zero x → ∀ R, le x R → ∀ k, le
    /// (abs (sinFnTerm k x)) (mul (expDominant (Nat.add (Nat.add k k) 1))
    /// (pow R (Nat.add (Nat.add k k) 1)))` — the [`Self::cos_fn_term_abs_le_wide`]
    /// analogue at the ODD index, via [`Self::exp_term_abs_le_dominant`] at
    /// `2k+1` (the pre-collapse bound `sin_term_abs_le_dominant`'s own proof
    /// computes internally, one step before its final collapse to
    /// `expDominant k` via `exp_dominant_odd_le`) plus
    /// [`Self::pow_le_pow_of_base_le`]. See `creal/trig_fn.rs`.
    pub sin_fn_term_abs_le_wide: NameId,
    /// `CReal.sinDominant16Over25 : Nat → CReal := fun k => mul (ofRat
    /// (natDivSucc 8 4)) (pow (ofRat (natDivSucc 16 24)) k)` — the
    /// dominating series for `sinFnTerm` at ratio `16/25`, mirroring
    /// [`Self::cos_dominant_16_over_25`] but at coefficient `R := 8/5`
    /// rather than `2`: the extra factor of `x` the odd exponent
    /// contributes collapses to `half · R = 4/5` at the bridge, and `2 ·
    /// (4/5) = 8/5 = R` is the coefficient here (verified by the same
    /// `Rat.normalize_mul_normalize`/`normalize_congr` route
    /// [`Self::pow_mul_distrib`]'s own bridge already uses, not assumed
    /// from the numeric coincidence). See `creal/trig_fn.rs`.
    pub sin_dominant_16_over_25: NameId,
    /// `CReal.sinDominant16Over25CauchyBody : sum_range_cauchy_body
    /// (sumRange sinDominant16Over25) K` for a concrete `K` — the raw,
    /// non-existential Cauchy witness [`Self::weierstrass_m_test`]'s
    /// `hcauchy` parameter needs, mirroring
    /// [`Self::cos_dominant_16_over_25_cauchy_body`] with `c := R` in place
    /// of `c := two`. See `creal/trig_fn.rs`.
    pub sin_dominant_16_over_25_cauchy_body: NameId,
    /// `CReal.sinFn : CReal → CReal` — general sine on the domain `[0,
    /// 8/5]`, by [`Self::weierstrass_m_test`] applied at `f := sinFnTerm`,
    /// `mseq := sinDominant16Over25`, `a := zero`, `b := ofRat (natDivSucc 8
    /// 4)`, mirroring [`Self::cos_fn_wide`]. See `creal/trig_fn.rs`.
    pub sin_fn: NameId,
    /// `CReal.sinFnUniformConverges : UniformConvergesOn (fun n x =>
    /// sumRange (fun k => sinFnTerm k x) n) sinFn zero (ofRat (natDivSucc 8
    /// 4))` — the M-test applied at sine's series, mirroring
    /// [`Self::cos_fn_wide_uniform_converges`]. See `creal/trig_fn.rs`.
    pub sin_fn_uniform_converges: NameId,
    /// `CReal.sinFnUniformlyContinuous : UniformlyContinuousOn sinFn zero
    /// (ofRat (natDivSucc 8 4))` — mirroring
    /// [`Self::cos_fn_wide_uniformly_continuous`]'s induction, with
    /// `sinFnTerm`'s own odd exponent `Nat.add (Nat.add k k) 1` in place of
    /// `Nat.add k k`. See `creal/trig_fn.rs`.
    pub sin_fn_uniformly_continuous: NameId,
    /// `CReal.sinFnLowerBoundOneToR : ∀ z, le one z → le z (ofRat (natDivSucc
    /// 8 4)) → le (ofRat (natDivSucc 1 3)) (sinFn z)` — pi rung 3
    /// (`docs/plan/status/169-pi.md`): a uniform lower bound `sin z >= 1/4`
    /// on `[1, 8/5]`.
    ///
    /// Sine's magnitude sequence `a k := expTerm (2k+1) * z^(2k+1)` is
    /// globally antitone on `[0, 8/5]` (`z^2 <= 64/25 <= 6 <= (2k+2)(2k+3)`
    /// for EVERY `k` — unlike cosine's own magnitude at `8/5`, no shift is
    /// needed), so [`Self::alternating_lower_bound`] applies directly at
    /// `m := 1`, giving `sin z >= z - z^3/6 >= 1 - (8/5)^3/6 = 119/375 >=
    /// 1/4`. The pointwise `Converges` fact `alternatingLowerBound` needs is
    /// built from domination
    /// ([`Self::sin_fn_term_abs_le_wide`]/[`Self::sum_range_converges_of_dominated`])
    /// and squeezed onto `sinFn z` via
    /// [`Self::close_within_of_within`]/[`Self::equiv_zero_of_rate`], the
    /// same technique `creal/trig_fn.rs`'s own `cos_limit_at_one_equiv_cos_one`
    /// uses for a NAMED target, generalized to an existential one. See
    /// `creal/trig_fn.rs`.
    pub sin_fn_lower_bound_one_to_r: NameId,
    /// `CReal.expTermSuccScale : ∀ m, Equiv (mul (ofNat (Nat.succ m))
    /// (expTerm (Nat.succ m))) (expTerm m)` — `(m+1)·(1/(m+1)!) = 1/m!`, the
    /// whole arithmetic content of the index-shifted coefficient identity
    /// underneath cosine's term-by-term derivative.
    ///
    /// Cheaper than [`Self::exp_term_antitone`] (the ORDER fact
    /// `1/(n+1)! ≤ 1/n!`, which needs a full `Int` cross-multiplication
    /// battery): `CReal.ofNat n` and `expTerm n` both unfold to
    /// `ofRat (Rat.normalize …)`, so `Rat.normalize_mul_normalize` fuses the
    /// product into ONE `normalize` and `Rat.normalize_congr` closes
    /// `(m+1)·1·m! = 1·(1·(m+1)!)` against `Nat.factorial_succ` alone.
    /// See `creal/trig_fn.rs`.
    pub exp_term_succ_scale: NameId,
    /// `CReal.cosFnTermDerivCoeff : ∀ j, Equiv (mul (cosTerm (Nat.succ j))
    /// (ofNat (Nat.succ (Nat.add (Nat.add j j) 1)))) (neg (sinTerm j))` —
    /// **the index-shifted coefficient identity** `cosTerm (j+1)·(2j+2) ~
    /// −sinTerm j` that makes the derivative of cosine's series sine's
    /// series, one index earlier.
    ///
    /// [`Self::exp_term_succ_scale`] at `m := 2j+1`, plus `(-1)^(j+1) ~
    /// -(-1)^j` — which is `pow`'s own ι-reduction `pow x (succ j) ≡ mul
    /// (pow x j) x` with `mul_neg_equiv`/`mul_one`, NOT a parity lemma. The
    /// one transport is `Nat.succ_add`, moving `cosTerm (succ j)`'s own
    /// exponent `Nat.add (succ j) (succ j)` to `Nat.succ (2j+1)`: `Nat.add`
    /// recurses on the RIGHT, so the two are propositionally but not
    /// definitionally equal at a symbolic `j`. See `creal/trig_fn.rs`.
    pub cos_fn_term_deriv_coeff: NameId,
    /// `CReal.cosFnTermHasDerivative : ∀ j, HasDerivativeOn (fun x =>
    /// cosFnTerm (Nat.succ j) x) (fun x => neg (sinFnTerm j x)) zero (ofRat
    /// (natDivSucc 8 4))` — cosine's series, differentiated one term at a
    /// time.
    ///
    /// [`Self::has_derivative_pow`] at `n := 2j+1` (so the FUNCTION's
    /// exponent is `2j+2`, never a truncating `Nat.sub`), then
    /// [`Self::has_derivative_smul`] at `c := cosTerm (succ j)`, then
    /// [`Self::has_derivative_congr`] onto the named shapes.
    /// `hasDerivative_pow`'s two Skolem `BoundedOn` functions are **computed,
    /// not extracted**: `creal/trig_fn.rs`'s own `pow` uniform continuity at
    /// a symbolic exponent through
    /// [`Self::bounded_of_uniformly_continuous`], lambda-abstracted over the
    /// exponent. See `creal/trig_fn.rs`.
    pub cos_fn_term_has_derivative: NameId,
    /// `CReal.cosFnPartialHasDerivative : ∀ n, HasDerivativeOn (fun x =>
    /// sumRange (fun k => cosFnTerm k x) (Nat.succ n)) (fun x => neg
    /// (sumRange (fun k => sinFnTerm k x) n)) zero (ofRat (natDivSucc 8 4))`
    /// — every partial sum of cosine's series differentiates to the negated
    /// partial sum of sine's series, ONE INDEX SHORTER.
    ///
    /// The `succ n`/`n` mismatch is forced, not cosmetic: `d/dx cosFnTerm 0`
    /// is `0`, so `n+1` cosine terms give `n` sine terms and any other
    /// statement would need `Nat.pred`. Induction over
    /// [`Self::has_derivative_add`]; `sumRange`'s own ι-reduction makes both
    /// FUNCTION sides definitionally equal, so
    /// [`Self::has_derivative_congr`] is needed only for the derivative
    /// residues (`neg zero ~ zero` at the base, `neg (A+B) ~ neg A + neg B`
    /// at the step). Together with
    /// [`Self::has_derivative_uniform_limit`] this is what a derivative for
    /// `cosFnWide` itself now needs — see `creal/trig_fn.rs`'s own section
    /// header for the two `UniformConvergesOn` re-indexings still missing.
    pub cos_fn_partial_has_derivative: NameId,
    /// `CReal.natDivSuccStepLe : ∀ (k n : Nat), Rat.le (Rat.natDivSucc k
    /// (Nat.succ n)) (Rat.natDivSucc k n)` — one-step antitonicity of
    /// `Rat.natDivSucc` in its INDEX, at a **symbolic numerator**.
    ///
    /// [`RatPrelude::nat_div_succ_antitone`] is this statement at numerator
    /// `1`, and its own doc comment records how much that one cost;
    /// [`RatPrelude::nat_div_succ_le_scaled`] reads a `(c+1)·n + c`-shaped
    /// index back to `n`, and `Nat.succ n` is not of that shape for any `c`
    /// leaving a bound that still shrinks in `n`. So neither covers a plain
    /// one-step shift at a general numerator — which is exactly what
    /// re-indexing a `UniformConvergesOn` witness by one needs.
    ///
    /// Closed with no new cross-multiplication:
    /// [`RatPrelude::nat_div_succ_mul`] factors `natDivSucc (k·1) j` as
    /// `natDivSucc k 0 · natDivSucc 1 j`, putting the index entirely in the
    /// second factor where the numerator-`1` antitonicity applies, and
    /// `Rat.mul_le_mul_of_nonneg_left` scales it back. Declared into the
    /// `CReal` namespace from `creal/trig_fn.rs` because `rat_prelude` is
    /// another lane's file; it belongs there.
    pub nat_div_succ_step_le: NameId,
    /// `CReal.uniformConvergesShift : ∀ F G a b, UniformConvergesOn F G a b →
    /// UniformConvergesOn (fun n => F (Nat.succ n)) G a b` — re-index a
    /// uniform-convergence witness by one. The rate is unchanged; the whole
    /// content is [`Self::nat_div_succ_step_le`] weakening the shifted
    /// family's own (tighter) bound at `succ n` back to `natDivSucc rate n`.
    /// See `creal/trig_fn.rs`.
    pub uniform_converges_shift: NameId,
    /// `CReal.uniformConvergesNeg : ∀ F G a b, UniformConvergesOn F G a b →
    /// UniformConvergesOn (fun n x => neg (F n x)) (fun x => neg (G x)) a b`.
    ///
    /// Every bound is unchanged. `creal/derivative.rs`'s
    /// `le_abs_neg_of_le_abs` bounds a negation by whatever bounds the
    /// original **without deciding a sign** — `abs` is not `Equiv`-invariant
    /// under `neg`, so this is not a congruence — and `neg_add_distrib`
    /// supplies the one algebraic step. See `creal/trig_fn.rs`.
    pub uniform_converges_neg: NameId,
    /// `CReal.cosFnWideHasDerivative : HasDerivativeOn cosFnWide (fun x =>
    /// neg (sinFn x)) zero (ofRat (natDivSucc 8 4))` — **cosine
    /// differentiates to minus sine on `[0, 8/5]`**.
    ///
    /// [`Self::has_derivative_uniform_limit`] at `F n := Sₙ₊₁`,
    /// `F' n := −Tₙ`, with [`Self::cos_fn_partial_has_derivative`] as the
    /// per-index hypothesis and the two re-indexed convergence witnesses
    /// ([`Self::uniform_converges_shift`], [`Self::uniform_converges_neg`]).
    /// Nothing is proved at this step that was not already built; it is the
    /// assembly. See `creal/trig_fn.rs`.
    pub cos_fn_wide_has_derivative: NameId,

    // --- general `exp : CReal → CReal` (creal/exp_fn.rs) -----------------------
    /// `creal/exp_fn.rs`'s own 4 names, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.exp_fn.exp_fn.exp_fn_term_abs_le` and documented in
    /// [`ExpFnNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub exp_fn: ExpFnNames,
    /// `CReal.maxRange : (Nat → CReal) → Nat → CReal` — the `max`-lattice
    /// analogue of [`Self::sum_range`]: `maxRange f 0 := f 0`, `maxRange f
    /// (succ n) := max (maxRange f n) (f (succ n))`, so `maxRange f n` is
    /// `max_{k≤n} f k`. See `creal/supremum.rs` — the finite-mesh-maximum
    /// primitive for the LUB family's honest row 1 (a uniformly continuous
    /// function's supremum on a compact interval), landed without the full
    /// `CReal.supOn` construction; that file's own module documentation
    /// records exactly what remains and why.
    pub max_range: NameId,
    /// `CReal.maxRange_zero : ∀ f, Eq CReal (maxRange f Nat.zero) (f
    /// Nat.zero)`. See `creal/supremum.rs`.
    pub max_range_zero: NameId,
    /// `CReal.maxRange_succ : ∀ f n, Eq CReal (maxRange f (Nat.succ n)) (max
    /// (maxRange f n) (f (Nat.succ n)))`. See `creal/supremum.rs`.
    pub max_range_succ: NameId,
    /// `CReal.maxRange_self_le : ∀ f n, le (f n) (maxRange f n)`. See
    /// `creal/supremum.rs`.
    pub max_range_self_le: NameId,
    /// `CReal.maxRange_mono : ∀ f m n, Nat.le m n → le (maxRange f m)
    /// (maxRange f n)`. See `creal/supremum.rs`.
    pub max_range_mono: NameId,
    /// `CReal.maxRange_ub : ∀ f n i, Nat.le i n → le (f i) (maxRange f n)`.
    /// See `creal/supremum.rs`.
    pub max_range_ub: NameId,
    /// `CReal.maxRange_transport : ∀ f g n n' e, (∀ i, Nat.le i n → Nat.le (e
    /// i) n') → (∀ i, Nat.le i n → Equiv (f i) (g (e i))) → le (maxRange f n)
    /// (maxRange g n')` — the general combinator route 2's nested-refinement
    /// construction needs (rung 3): comparing two DIFFERENT `maxRange` folds
    /// — different sampling function, different bound — related by an
    /// index-embedding `e` under which `f`'s samples are `Equiv` to `g`'s.
    /// **Not** an instance of [`Self::mono_of_le_succ`] (that combinator
    /// holds the sampling function fixed); proved instead by induction on an
    /// auxiliary index `k ≤ n`, base case via [`Self::max_range_ub`] plus
    /// [`Self::le_congr`], step case via [`Self::max_le`] combining the
    /// inductive hypothesis with a fresh `maxRange_ub` instance. See
    /// `creal/supremum.rs`.
    pub max_range_transport: NameId,
    /// `CReal.meshLevelCount : Nat → Nat` — the geometric (doubling) mesh-count
    /// schedule route 2's nested refinement runs on: `meshLevelCount 0 :=
    /// 0`, `meshLevelCount (succ j) := succ (add (meshLevelCount j)
    /// (meshLevelCount j))`, i.e. `meshLevelCount j = 2^j − 1`, built
    /// additively so no `Nat.mul` dependency is needed. See
    /// `creal/supremum.rs`.
    pub mesh_level_count: NameId,
    /// `CReal.meshLevelCount_zero : Eq Nat (meshLevelCount Nat.zero) Nat.zero`.
    /// See `creal/supremum.rs`.
    pub mesh_level_count_zero: NameId,
    /// `CReal.meshLevelCount_succ : ∀ j, Eq Nat (meshLevelCount (succ j)) (succ
    /// (add (meshLevelCount j) (meshLevelCount j)))`. See
    /// `creal/supremum.rs`.
    pub mesh_level_count_succ: NameId,
    /// `CReal.meshLevelCount_pow : ∀ j, Eq Nat (Nat.succ (meshLevelCount j))
    /// (Nat.pow 2 j)` — the doubling schedule's formal, subtraction-free
    /// relation to `Nat.pow` (`meshLevelCount j = 2^j − 1`, restated as `+1`
    /// on the left), proved by induction. Needed to route
    /// `Nat.lt_pow_size`'s power-of-two dominance bound back into a
    /// concrete mesh LEVEL via `Nat.size`. See `creal/supremum.rs`'s
    /// `CReal.hclose_of_uc`.
    pub mesh_level_count_pow: NameId,
    /// `CReal.meshLevelCount_ge_of_size : ∀ (c outer j : Nat),
    /// Nat.le (Nat.add (Nat.size c) (Nat.size outer)) j →
    /// Nat.le (Nat.add (Nat.mul (Nat.succ c) outer) c) (meshLevelCount j)` —
    /// rung 6c's `Nat` half: at which mesh LEVEL does the doubling schedule
    /// reach [`Self::mesh_le_of_ge`]'s Archimedean threshold?
    ///
    /// The threshold is `(bound(b−a)+1)·outer + bound(b−a)`, so the question
    /// is `2^j ≥ (c+1)·(outer+1)`, and `Nat.lt_pow_size` answers it one
    /// factor at a time: `size c` covers `c+1`, `size outer` covers
    /// `outer+1`, and `Nat.pow_add` turns their SUM in the exponent into the
    /// PRODUCT of the two bounds. Additive, so it composes with
    /// [`Self::true_exp_of_modulus`]'s own accumulator without introducing a
    /// `Nat.mul` into the schedule; the one `Nat.mul` here is inside the
    /// threshold `mesh_le_of_ge` already states. See `creal/supremum.rs`.
    pub mesh_level_count_ge_of_size: NameId,
    /// `CReal.meshMax : (CReal → CReal) → CReal → CReal → Nat → CReal :=
    /// fun F a b j => maxRange (fun i => F (meshSamplePoint a (meshDelta a b
    /// (meshLevelCount j)) i)) (meshLevelCount j)` — the level-`j` mesh
    /// maximum of `F` on `[a, b]`. See `creal/supremum.rs`.
    pub mesh_max: NameId,
    /// `CReal.meshMax_step_le : ∀ F a b j, UniformlyContinuousOn F a b → le a
    /// b → le (meshMax F a b j) (meshMax F a b (Nat.succ j))` — rung 3 of the
    /// `supOn` route: adjacent mesh levels are ordered. Instantiates
    /// [`Self::max_range_transport`] at the two mesh samplers with index
    /// embedding `e i := add i i`; the `Equiv` hypothesis it needs is closed
    /// by [`Self::congr_of_uniformly_continuous`] against a point-level
    /// `Equiv` (the coarse sample at `i` equals the fine sample at `2i`,
    /// since `meshLevelCount`'s doubling schedule makes the two meshes nest
    /// exactly). See `creal/supremum.rs`.
    pub mesh_max_step_le: NameId,
    /// `CReal.meshMax_mono : ∀ F a b, UniformlyContinuousOn F a b → le a b →
    /// ∀ j j', Nat.le j j' → le (meshMax F a b j) (meshMax F a b j')` — rung
    /// 4, general monotonicity across mesh levels, free from rung 3 via
    /// [`Self::mono_of_le_succ`], exactly [`Self::max_range_mono`]'s own
    /// construction one level up. See `creal/supremum.rs`.
    pub mesh_max_mono: NameId,
    /// `CReal.expOfModulus : (Nat → Nat) → Nat → Nat := fun m k => Nat.size
    /// (m (meshLevelCount k))` — rung 5 of the `supOn` route, the
    /// power-of-two exponent request `Nat.lt_pow_size` needs to dominate an
    /// arbitrary modulus value `m (meshLevelCount k)` with no `Nat.div` or
    /// search. Generic over `m` rather than tied to a specific
    /// `UniformlyContinuousOn` witness, so it applies at `m :=
    /// UniformlyContinuousOn.modulus F a b u` at the use site. See
    /// `creal/supremum.rs`.
    pub exp_of_modulus: NameId,
    /// `CReal.trueExpOfModulus : (Nat → Nat) → Nat → Nat`, `trueExpOfModulus
    /// m 0 := expOfModulus m 0`, `trueExpOfModulus m (succ k) :=
    /// add (trueExpOfModulus m k) (expOfModulus m (succ k))` — the
    /// running-sum accumulator that forces monotonicity onto
    /// [`Self::exp_of_modulus`]'s own not-necessarily-monotone sequence.
    /// Built with `Nat.add`, never `Nat.max`: this kernel's `Nat` prelude has
    /// no `Nat.max`. See `creal/supremum.rs`.
    pub true_exp_of_modulus: NameId,
    /// `CReal.trueExpOfModulus_zero : ∀ m, Eq Nat (trueExpOfModulus m
    /// Nat.zero) (expOfModulus m Nat.zero)`. See `creal/supremum.rs`.
    pub true_exp_of_modulus_zero: NameId,
    /// `CReal.trueExpOfModulus_succ : ∀ m k, Eq Nat (trueExpOfModulus m
    /// (succ k)) (add (trueExpOfModulus m k) (expOfModulus m (succ k)))`.
    /// See `creal/supremum.rs`.
    pub true_exp_of_modulus_succ: NameId,
    /// `CReal.trueExpOfModulus_step_le : ∀ m k, Nat.le (trueExpOfModulus m
    /// k) (trueExpOfModulus m (succ k))` — the adjacent-step half of
    /// monotonicity, via [`Self::true_exp_of_modulus_succ`]'s ι-reduction
    /// plus `Nat.le_add_right`. See `creal/supremum.rs`.
    pub true_exp_of_modulus_step_le: NameId,
    /// `CReal.trueExpOfModulus_mono : ∀ m j j', Nat.le j j' → Nat.le
    /// (trueExpOfModulus m j) (trueExpOfModulus m j')` — general
    /// monotonicity, free from [`Self::true_exp_of_modulus_step_le`] via
    /// `Nat.monotone_of_le_succ`, the `Nat`-level twin of
    /// [`Self::mono_of_le_succ`]. See `creal/supremum.rs`.
    pub true_exp_of_modulus_mono: NameId,
    /// `CReal.expOfModulus_le_trueExpOfModulus : ∀ m k, Nat.le
    /// (expOfModulus m k) (trueExpOfModulus m k)` — the accumulator is
    /// always at least as fine as the single level it was built to cover,
    /// via `Nat.le_add_right` read through `Nat.add_comm`
    /// (`crate::rat_prelude::ops::nat_rewrite_prop`); needed by rung 6's
    /// per-level gap bound. See `creal/supremum.rs`.
    pub exp_of_modulus_le_true_exp_of_modulus: NameId,
    /// `CReal.meshPoint_near_coarse : forall a b j, le a b -> forall d i',
    /// Nat.le i' (meshLevelCount (Nat.add j d)) ->
    /// exists i, Nat.le i (meshLevelCount j) /\ le (P j i) (P (add j d) i') /\
    /// le (add (P (add j d) i') (D (add j d))) (add (P j i) (D j))`, where
    /// `P L i := meshSamplePoint a (meshDelta a b (meshLevelCount L)) i` and
    /// `D L := meshDelta a b (meshLevelCount L)` -- the MULTI-LEVEL
    /// nearest-mesh-point lemma: every level-`(j+d)` mesh point, at any
    /// refinement depth, lies in one level-`j` cell, between that cell's left
    /// endpoint and one coarse width above it. Rung 6's missing piece (see
    /// `creal/supremum.rs`'s module documentation): the depth-1 case is
    /// [`Self::mesh_max_step_le`]'s exact even-index coincidence, and this is
    /// the arbitrary-depth statement it does not give. Needs no `Nat`
    /// division -- the conclusion is `Prop`, so the coarse index is an
    /// `Exists` witness the induction step re-eliminates, and the parity split
    /// is `Nat.even_or_odd`'s computed half.
    pub mesh_point_near_coarse: NameId,
    /// `CReal.maxRange_le_add_of_exists : forall f g n n' eps,
    /// (forall i, Nat.le i n -> exists i', Nat.le i' n' /\ le (f i) (add (g i') eps))
    /// -> le (maxRange f n) (add (maxRange g n') eps)` -- the APPROXIMATE,
    /// existential-witnessed form of [`Self::max_range_transport`]: the
    /// per-index relation is a `le ... + eps` estimate rather than an `Equiv`,
    /// and the coarse index arrives as an `Exists` witness rather than as a
    /// supplied `e : Nat -> Nat`. The second is what lets
    /// [`Self::mesh_point_near_coarse`] plug in directly, with no `Nat`
    /// quotient/remainder algebra: the conclusion is `Prop`, so `Exists.rec`
    /// applies. See `creal/supremum.rs`.
    pub max_range_le_add_of_exists: NameId,
    /// `CReal.meshMax_le_add_of_step_close : forall F a b j d eps, le a b ->
    /// (forall x y, le a x -> le x b -> le a y -> le y b -> le x y ->
    ///  le y (add x (meshDelta a b (meshLevelCount j))) ->
    ///  le (F y) (add (F x) eps)) ->
    /// le (meshMax F a b (Nat.add j d)) (add (meshMax F a b j) eps)` -- rung
    /// 6's GAP BOUND at arbitrary refinement depth, with the accuracy schedule
    /// factored out. All the mesh geometry is discharged here; what a `supOn`
    /// assembly still owes is only the instantiation of `hclose` from
    /// [`Self::uc_spec`] at the accuracy [`Self::exp_of_modulus`] selects. The
    /// hypothesis is deliberately ONE-SIDED (how far `F` may RISE across a
    /// rightward step of at most one level-`j` cell): the other direction is
    /// [`Self::mesh_max_mono`]. See `creal/supremum.rs`.
    pub mesh_max_le_add_of_step_close: NameId,
    /// `CReal.meshMax_le_add_of_modulus : ∀ F a b (u : UniformlyContinuousOn
    /// F a b) (n j d : Nat), le a b → Nat.le (Nat.add (Nat.size (CReal.bound
    /// (add b (neg a)))) (Nat.size (UniformlyContinuousOn.modulus F a b u
    /// n))) j → le (meshMax F a b (Nat.add j d)) (add (meshMax F a b j)
    /// (ofRat (Rat.natDivSucc 1 n)))` — **the obligation
    /// [`Self::mesh_max_le_add_of_step_close`]'s own documentation names as
    /// all a `supOn` assembly still owes, discharged.**
    ///
    /// `hclose` instantiated from [`Self::uc_spec`]. No mesh geometry
    /// survives into the hypothesis: the sole condition is a `Nat` bit-count
    /// inequality on the level `j`, routed through
    /// [`Self::mesh_level_count_ge_of_size`] into
    /// [`Self::mesh_le_of_ge`]'s Archimedean threshold, so the interval width
    /// is handled by `CReal.bound` and never by an existential.
    ///
    /// `eps` is `1/(n+1)` at a FREELY CHOSEN `n`, which is what makes the
    /// telescope summable: a caller takes `n := meshLevelCount k`, giving
    /// `eps = 1/2^k` (rung 5's doubling schedule reused as the requested
    /// ACCURACY index), so the harmonic-series trap never arises. Nothing
    /// here forces that choice. See `creal/supremum.rs`.
    pub mesh_max_le_add_of_modulus: NameId,
    /// `CReal.supLevel : ∀ F a b, UniformlyContinuousOn F a b → Nat → Nat :=
    /// fun F a b u k => Nat.add (Nat.size (CReal.bound (add b (neg a))))
    /// (trueExpOfModulus (UniformlyContinuousOn.modulus F a b u) k)` — the
    /// mesh level the sup sequence samples at accuracy index `k`.
    ///
    /// One summand per factor of
    /// [`Self::mesh_level_count_ge_of_size`]'s threshold: the interval WIDTH
    /// (constant in `k`) and the MODULUS at the requested accuracy. Additive
    /// so [`Self::exp_of_modulus_le_true_exp_of_modulus`] composes with
    /// `Nat.add_le_add_left`. The width term is what
    /// [`Self::exp_of_modulus`]'s own schedule does not carry.
    /// See `creal/supremum.rs`.
    pub sup_level: NameId,
    /// `CReal.supLevel_mono : ∀ F a b u k k', Nat.le k k' →
    /// Nat.le (supLevel F a b u k) (supLevel F a b u k')`.
    /// See `creal/supremum.rs`.
    pub sup_level_mono: NameId,
    /// `CReal.supSeq : ∀ F a b, UniformlyContinuousOn F a b → Nat → CReal :=
    /// fun F a b u k => meshMax F a b (supLevel F a b u k)` — the sequence
    /// whose limit is the supremum of `F` on `[a, b]`.
    ///
    /// **A VALUE, never an argmax.** Each term is a finite maximum over a
    /// mesh, so it is a height; nothing here names a point attaining it, and
    /// [`ExtremeValueNames::evt_attained_max_decides_sign`] says no construction can.
    /// See `creal/supremum.rs`.
    pub sup_seq: NameId,
    /// `CReal.supSeq_mono : ∀ F a b u, le a b → ∀ k k', Nat.le k k' →
    /// le (supSeq F a b u k) (supSeq F a b u k')` — the lower half of the
    /// Cauchy estimate, exact (no epsilon): refining a mesh only adds sample
    /// points. See `creal/supremum.rs`.
    pub sup_seq_mono: NameId,
    /// `CReal.supSeq_le_add : ∀ F a b u, le a b → ∀ k k', Nat.le k k' →
    /// le (supSeq F a b u k') (add (supSeq F a b u k) (ofRat (natDivSucc 1
    /// (meshLevelCount k))))` — the upper half, at the geometric rate
    /// `1/2^k`.
    ///
    /// **One application of [`Self::mesh_max_le_add_of_modulus`], not a
    /// telescope**, because that gap bound is uniform in refinement depth:
    /// however many doublings `trueExpOfModulus` jumps between `k` and `k'`,
    /// one epsilon covers all of them. `Nat.le_dest` supplies the `add j d`
    /// shape, an `Exists.rec` into a `Prop` — permitted; the data restriction
    /// bites only at `supOn`'s own `CReal.mk`. See `creal/supremum.rs`.
    pub sup_seq_le_add: NameId,
    /// `CReal.le_meshLevelCount : ∀ (m : Nat), Nat.le m (meshLevelCount m)` —
    /// `m ≤ 2^m − 1`, the doubling schedule outrunning its own index. This is
    /// the geometric-to-harmonic step: it is what lets the summable request
    /// `1/2^k` be WEAKENED to the `1/(k+1)` a Cauchy modulus is stated in.
    /// See `creal/supremum.rs`.
    pub le_mesh_level_count: NameId,
    /// `CReal.supSeq_abs_diff_le : ∀ F a b u, le a b → ∀ m n, le (abs (add
    /// (supSeq F a b u m) (neg (supSeq F a b u n)))) (ofRat (Rat.add
    /// (natDivSucc 1 m) (natDivSucc 1 n)))` — the two-sided estimate in
    /// exactly [`Self::cauchy_of_abs_diff_le`]'s shape, at `K := 1`.
    ///
    /// `Nat.le_total` splits on which index is coarser. In each branch the
    /// easy side is [`Self::sup_seq_mono`] and the working side is
    /// [`Self::sup_seq_le_add`] weakened through
    /// [`Self::le_mesh_level_count`]. `K = 1` is what the geometric schedule
    /// buys, not a tuning choice. See `creal/supremum.rs`.
    pub sup_seq_abs_diff_le: NameId,
    /// `CReal.supSeq_cauchy : ∀ F a b u, le a b → Cauchy (supSeq F a b u)` —
    /// **the mesh maxima of a uniformly continuous function on a compact
    /// interval converge.**
    ///
    /// EVT's constructive content as a `Prop`. Producing the supremum itself
    /// as DATA is the separate `CReal.mk`/[`Self::speedup`] step, which needs
    /// the same estimate restated on canonical SAMPLES rather than as a
    /// real-valued bound. See `creal/supremum.rs`.
    pub sup_seq_cauchy: NameId,
    /// `CReal.supOn : ∀ F a b, le a b → UniformlyContinuousOn F a b → CReal`
    /// — **the supremum of a uniformly continuous function on a compact
    /// interval, produced rather than asserted to exist.**
    ///
    /// EVT's row 1 under ADR-0603's grading. Row 2,
    /// [`ExtremeValueNames::evt_attained_max_decides_sign`], proves a MAXIMISER cannot be
    /// constructed; this is the maximum's VALUE, which can. Nothing here names
    /// a point attaining it, and nothing should.
    ///
    /// `CReal.mk (speedup (diagonal (supSeq F a b u)) 3)
    /// (regular_of_scaled_cauchy … )`, `integral.rs`'s own shape one
    /// construction over. `K := 3` is forced:
    /// [`Self::sup_seq_abs_diff_le`] gives `K = 1` and
    /// [`Self::scaled_cauchy_of_abs_diff_le`]'s index shift costs `+2`.
    ///
    /// **Hypotheses, honestly.** `le a b`, and a `UniformlyContinuousOn`
    /// witness whose modulus is DATA — the constructive substitute for
    /// "continuous on a compact set", which no constructive development can
    /// derive from pointwise continuity. There is no Archimedean hypothesis
    /// and no positivity side condition: the interval width is handled by
    /// [`Self::bound`] inside [`Self::mesh_le_of_ge`].
    /// See `creal/supremum.rs`.
    pub sup_on: NameId,
    /// `CReal.supSeq_converges_supOn : ∀ F a b (hab : le a b) u,
    /// Converges (supSeq F a b u) (supOn F a b hab u)` — **`supOn` is the
    /// limit of the mesh maxima, not merely a well-typed `CReal.mk`.**
    ///
    /// The kernel accepting a `Definition` says nothing about what it
    /// computes; this is the theorem that pins `supOn` to the thing it is
    /// supposed to be. One application of
    /// [`Self::converges_of_scaled_cauchy`], whose conclusion NAMES the same
    /// `CReal.mk` term `supOn`'s body builds — the identical `ExprId`, so the
    /// kernel never unfolds the `Definition` to compare the two sides.
    /// See `creal/supremum.rs`.
    pub sup_seq_converges_sup_on: NameId,
    /// `CReal.maxRange_attained_approx : ∀ (f : Nat → CReal) (n e : Nat),
    /// ∃ i, Nat.le i n ∧ le (maxRange f n) (add (f i) (ofRat (Rat.natDivSucc
    /// 1 e)))` — a finite maximum is APPROXIMATELY attained at one of its
    /// samples.
    ///
    /// The exact form is not available and must not be attempted: choosing
    /// which sample attains the maximum decides `le x y ∨ le y x` for
    /// arbitrary reals. The `1/(e+1)` slack buys the decision back through
    /// [`Self::lt_cotrans`]. See `creal/sup_laws.rs`.
    pub max_range_attained_approx: NameId,
    /// `CReal.supSeq_le_shift : ∀ F a b u, le a b → ∀ k n, le (supSeq F a b u
    /// n) (add (supSeq F a b u k) (ofRat (Rat.natDivSucc 1 (meshLevelCount
    /// k))))` — every term of the sup sequence is within `1/2^k` of the `k`-th
    /// term, in WHICHEVER direction.
    ///
    /// [`Self::sup_seq_le_add`] is the `n ≥ k` half; the other half is free
    /// from [`Self::sup_seq_mono`]. Needed because `converges_upper_bound`
    /// asks for a bound at every index. See `creal/sup_laws.rs`.
    pub sup_seq_le_shift: NameId,
    /// `CReal.supOn_approx_lub : ∀ F a b (hab : le a b) (u :
    /// UniformlyContinuousOn F a b) (e : Nat), ∃ x, le a x ∧ (le x b ∧
    /// le (supOn F a b hab u) (add (F x) (ofRat (Rat.natDivSucc 1 e))))` —
    /// **the constructive least-upper-bound law**, EVT's row 1 second half.
    ///
    /// `supOn` is approached by values of `F` on `[a, b]` to any requested
    /// accuracy, at a point the proof exhibits. It is NOT attained, and the
    /// exact form is REFUTED rather than unproved —
    /// [`ExtremeValueNames::evt_attained_max_decides_sign`] shows an attaining maximiser
    /// would decide the sign of an arbitrary real. That is why this statement
    /// is approximate and must stay so. See `creal/sup_laws.rs`.
    pub sup_on_approx_lub: NameId,
    /// `CReal.supSeq_le_supOn : ∀ F a b (hab : le a b) u k,
    /// le (supSeq F a b u k) (supOn F a b hab u)` — every mesh maximum is
    /// below the supremum, EXACTLY, with no epsilon.
    ///
    /// [`Self::sup_seq_mono`] under [`Self::converges_lower_bound_shift`] at
    /// shift `k`: the unshifted `converges_lower_bound` wants the bound at
    /// every index including those below `k`, where it is false. See
    /// `creal/sup_laws.rs`.
    pub sup_seq_le_sup_on: NameId,
    /// `CReal.supOn_ub_at_supSeq_point : ∀ F a b (hab : le a b) u k i,
    /// Nat.le i (meshLevelCount (supLevel F a b u k)) →
    /// le (F (meshSamplePoint a (meshDelta a b (meshLevelCount (supLevel F a b
    /// u k))) i)) (supOn F a b hab u)` — **the upper-bound law at every point
    /// the construction samples.**
    ///
    /// [`Self::max_range_ub`] then [`Self::sup_seq_le_sup_on`]. NOT stated at
    /// an arbitrary mesh level: nothing proves `supLevel`'s schedule is
    /// cofinal in the levels (`trueExpOfModulus` accumulates `expOfModulus`,
    /// which is `0` whenever the modulus is). Pairs with
    /// [`Self::sup_on_approx_lub`], whose witness is a point of exactly this
    /// family. See `creal/sup_laws.rs`.
    pub sup_on_ub_at_sup_seq_point: NameId,
    /// `CReal.stepFamily_locate : ∀ (P : Nat → CReal) (w eps : CReal),
    /// le zero w → lt zero eps → (∀ i, le (P (Nat.succ i)) (add (P i) w)) →
    /// ∀ (n : Nat) (t : CReal), le (P Nat.zero) t →
    /// le t (add (add (P n) w) eps) →
    /// ∃ i, Nat.le i n ∧ (le (P i) (add t eps) ∧ le t (add (add (P i) w) eps))`
    /// — **cell location**: a real lying under a finite increasing family is
    /// located, to within one step plus `eps`, at one member of it.
    ///
    /// Locating a real EXACTLY in a cell would decide `le x y ∨ le y x`;
    /// locating it to within `eps` is constructive, by [`Self::lt_cotrans`],
    /// and `eps` is absorbed by uniform continuity at the caller. Stated over
    /// the ORDER alone — no `meshDelta`, no `CReal.mul`, no `CReal.ofNat` —
    /// so the mesh version is an instantiation with three interface
    /// identities and the induction carries no ring algebra. See
    /// `creal/sup_laws.rs`.
    pub step_family_locate: NameId,
    /// `CReal.meshMax_le_supOn_add : ∀ F a b (hab : le a b) u k dd,
    /// le (meshMax F a b (Nat.add (supLevel F a b u k) dd))
    ///    (add (supOn F a b hab u) (ofRat (Rat.natDivSucc 1 (meshLevelCount
    /// k))))` — **`supOn` dominates the mesh maximum at EVERY level above the
    /// schedule, to within `1/2^k`.**
    ///
    /// The way around the cofinality gap
    /// [`Self::sup_on_ub_at_sup_seq_point`] documents:
    /// [`Self::mesh_max_le_add_of_modulus`] is depth-uniform, so an arbitrary
    /// level ABOVE one scheduled level costs one epsilon however deep the
    /// refinement goes. See `creal/sup_laws.rs`.
    pub mesh_max_le_sup_on_add: NameId,
    /// `CReal.supOn_ub_at_fine_mesh_point : ∀ F a b (hab : le a b) u k dd i,
    /// Nat.le i (meshLevelCount (Nat.add (supLevel F a b u k) dd)) →
    /// le (F (meshSamplePoint a (meshDelta a b (meshLevelCount (Nat.add
    /// (supLevel F a b u k) dd))) i)) (add (supOn F a b hab u) (ofRat
    /// (Rat.natDivSucc 1 (meshLevelCount k))))` — **the upper-bound law on a
    /// family of points that can be made as fine as wanted, at an epsilon
    /// chosen independently of the fineness.**
    ///
    /// [`Self::max_range_ub`] then [`Self::mesh_max_le_sup_on_add`]. Strictly
    /// stronger than [`Self::sup_on_ub_at_sup_seq_point`], which is the
    /// `dd = 0` case with the epsilon dropped. See `creal/sup_laws.rs`.
    pub sup_on_ub_at_fine_mesh_point: NameId,
    /// `CReal.supOn_ub : ∀ F a b (hab : le a b) (u : UniformlyContinuousOn F
    /// a b) (x : CReal), le a x → le x b → le (F x) (supOn F a b hab u)` —
    /// **the upper-bound law at an ARBITRARY point of `[a, b]`, which is what
    /// makes `supOn` a supremum rather than a limit of mesh maxima.**
    ///
    /// With [`Self::sup_on_approx_lub`] this is the pair that characterizes
    /// `supOn`: it dominates every value of `F` on `[a, b]`, and it is
    /// approached by them to any requested accuracy. Neither produces an
    /// argmax and neither may — [`ExtremeValueNames::evt_attained_max_decides_sign`] proves
    /// an attaining maximiser would decide the sign of an arbitrary real.
    ///
    /// [`Self::step_family_locate`] places `x` within one mesh cell plus an
    /// `eps` of a sampled point; the margin `supLevel`'s zero-slack schedule
    /// does not have is bought in two independent places (an arbitrary level
    /// above a scheduled one, and asking the mesh for one HALVING more
    /// accuracy than the modulus demands), then
    /// [`Self::sup_on_ub_at_fine_mesh_point`] bounds the sampled value. See
    /// `creal/sup_laws.rs`.
    pub sup_on_ub: NameId,
    /// `creal/evt_row1.rs`'s own name, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.evt_row1.evt_approx_max` and documented in
    /// [`EvtRow1Names`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub evt_row1: EvtRow1Names,
    /// `CReal.abs_diff_le_of_deriv_bound : ∀ F F' a b, HasDerivativeOn F F'
    /// a b → ∀ M, (∀ z, le a z → le z b → le (abs (F' z)) M) → ∀ x y,
    /// le a x → le x y → le y b →
    /// le (abs (add (F y) (neg (F x)))) (mul M (add y (neg x)))`
    /// (`creal/derivative.rs`) — **the mean value INEQUALITY**: a derivative
    /// bounded in magnitude by `M` on `[a,b]` makes `F` Lipschitz there with
    /// constant `M`.
    ///
    /// No new analysis. It is [`Self::monotone_of_nonneg_deriv`] — which
    /// already owns the subdivide-and-telescope construction — applied TWICE,
    /// to `r ↦ M·r − F(r)` and `r ↦ M·r + F(r)`, whose derivatives are
    /// `M ∓ F'` and are nonnegative exactly when `|F'| ≤ M`; the two
    /// conclusions are the two branches [`Self::abs_le`] consumes. The linear
    /// map's derivative witness is `creal/mvt.rs`'s own `build_hd_linear`
    /// (no magnitude bound on `M` needed, unlike
    /// [`Self::has_derivative_smul`]), and everything else is the ring algebra
    /// already private to `creal/derivative.rs`.
    ///
    /// Stated with `le x y` (not `Apart`, not `abs` on the right): the
    /// hypotheses already order the pair, matching
    /// [`Self::diff_le_of_strict_mono_magnitude`]'s house shape one direction
    /// over — that lemma bounds the DOMAIN gap from a derivative floor, this
    /// one bounds the IMAGE gap from a derivative ceiling.
    ///
    /// This is the step a "uniform limit of derivatives" theorem needs and
    /// this development does not have: term-by-term differentiation of a
    /// power series bounds `(Fₖ − Fₙ)(y) − (Fₖ − Fₙ)(x)` by
    /// `sup|Fₖ' − Fₙ'|·|y − x|`, which is exactly this inequality applied to
    /// the tail. See `creal/derivative.rs`'s own section header for what is
    /// still missing above it.
    pub abs_diff_le_of_deriv_bound: NameId,
    /// `CReal.lipschitz_of_deriv_bound : ∀ F F' a b, HasDerivativeOn F F' a b →
    /// ∀ M, le zero M → (∀ z, le a z → le z b → le (abs (F' z)) M) → ∀ x y,
    /// le a x → le x b → le a y → le y b →
    /// le (abs (add (F y) (neg (F x)))) (mul M (abs (add y (neg x))))`
    /// (`creal/derivative.rs`) — [`Self::abs_diff_le_of_deriv_bound`] with its
    /// endpoints **unordered**, which is the form a derivative consumer can
    /// actually use: `deriv_spec_body` quantifies `x` and `y` independently
    /// over `[a, b]`, and `le x y ∨ le y x` is a decision on the sign of a real
    /// this development does not have.
    ///
    /// No case split, and no lattice identity. `u := min x y` lies below BOTH
    /// endpoints and inside `[a, b]` ([`Self::le_min`] from `a ≤ x`, `a ≤ y`),
    /// so the ordered inequality applies to `(u, x)` and to `(u, y)`
    /// separately and the triangle inequality through `F u` gives
    /// `|F y − F x| ≤ M·((y − u) + (x − u))`. The constant stays EXACT because
    /// `(y − u) + (x − u) ≤ |y − x|` follows from the meet's universal property
    /// alone — three [`Self::le_min`] applications whose legs are
    /// [`Self::le_abs_self`], [`Self::neg_le_abs`] + [`Self::neg_sub_swap`],
    /// and [`Self::abs_nonneg`] — so `min` is never unfolded to its pointwise
    /// `Rat.min` representation.
    ///
    /// `le zero M` is not removable: the last step multiplies the domain bound
    /// through by `M` ([`Self::mul_le_mul_of_nonneg_left`]). It is free for
    /// every caller, `M` being a magnitude bound, but deriving it here would
    /// need `le a b` to have a point to evaluate at.
    ///
    /// This is the tail estimate a "uniform limit of derivatives" theorem
    /// needs: `Fₖ − Fₙ` has derivative `Fₖ' − Fₙ'`, uniformly small, and the
    /// pair `(x, y)` it must be applied at comes from `deriv_spec_body` in no
    /// particular order.
    pub lipschitz_of_deriv_bound: NameId,
    /// `CReal.abs_diff_sub_le_of_deriv_bound : ∀ F F' G G' a b,
    /// HasDerivativeOn F F' a b → HasDerivativeOn G G' a b → ∀ M, le zero M →
    /// (∀ z, le a z → le z b → le (abs (add (F' z) (neg (G' z)))) M) → ∀ x y,
    /// le a x → le x b → le a y → le y b →
    /// le (abs (add (add (F y) (neg (F x))) (neg (add (G y) (neg (G x))))))
    ///    (mul M (abs (add y (neg x))))`
    /// (`creal/derivative.rs`) — **the tail estimate** a term-by-term
    /// differentiation needs: two increments differ by at most the uniform gap
    /// between the derivatives times the domain gap.
    ///
    /// Three moves, no new analysis. [`Self::has_derivative_sub`] gives
    /// `HasDerivativeOn (F − G) (F' − G')` — and because it builds its
    /// functions as `fun r => add (F r) (neg (G r))` verbatim, the derivative
    /// bound needs no transport at all, only re-wrapping. Then
    /// [`Self::lipschitz_of_deriv_bound`] (and it must be that one, not
    /// [`Self::abs_diff_le_of_deriv_bound`]: `deriv_spec_body` hands its
    /// consumer an unordered `(x, y)`). Then one commutative-group
    /// rearrangement `(F y − G y) − (F x − G x) ~ (F y − F x) − (G y − G x)` —
    /// the Lipschitz bound is about the difference FUNCTION at two points, the
    /// series argument needs the difference of two INCREMENTS.
    ///
    /// This is the bound that the uniform convergence of the FUNCTIONS cannot
    /// supply: that route bounds the same quantity by a CONSTANT `2δₙ`, while
    /// `deriv_spec_body`'s budget is `ε·|y − x|` over every `y` arbitrarily
    /// close to `x`, and no `n` absorbs a constant into it.
    pub abs_diff_sub_le_of_deriv_bound: NameId,
    /// `CReal.hasDerivative_uniform_limit : ∀ (F F' : Nat → CReal → CReal)
    /// (G G' : CReal → CReal) (a b : CReal),
    /// (∀ n, HasDerivativeOn (F n) (F' n) a b) →
    /// UniformConvergesOn F G a b → UniformConvergesOn F' G' a b →
    /// HasDerivativeOn G G' a b`
    /// (`creal/uniform_convergence.rs`) — **the interchange of limit and
    /// derivative**, and the first declaration in this development to conclude
    /// `HasDerivativeOn` from anything other than a pointwise combinator.
    ///
    /// The modulus is the chosen member's own at a three-way-split accuracy:
    /// `sidx e := 3e+2` and `nidx e := (r'+1)·(sidx e) + r'`, the latter being
    /// exactly `uniform_convergence.rs`'s `weaken_rate` index, so the
    /// derivative series' rate at `nidx e` is at most `1/(3e+3)` by that
    /// function's own proof. `Rat.natDivSucc_add` twice plus
    /// `Rat.natDivSucc_scale` at `c := 2` fuses the three legs back to
    /// `1/(e+1)`.
    ///
    /// The interesting leg is `(G y − G x) − (Sₙ y − Sₙ x)`, which uniform
    /// convergence of the FUNCTIONS bounds only by a CONSTANT `2δₙ` — useless
    /// against `deriv_spec_body`'s `ε·|y − x|` budget over `y` arbitrarily
    /// close to `x`. It is routed instead through
    /// [`Self::abs_diff_sub_le_of_deriv_bound`] on the tail `Fₖ − Sₙ`, with
    /// [`Self::le_of_forall_le_add_small`] removing the `k → ∞` slack and
    /// `Rat.natDivSucc_le_one` (`|y − x| ≤ 1`) letting the two function legs
    /// be paid in a purely rational budget.
    ///
    /// Nothing here inspects a sequence element: every fact used about `F` and
    /// `F'` is one of the two [`Self::uconv_spec`]s or the per-index
    /// `HasDerivativeOn`, so this applies verbatim to a power series' partial
    /// sums once those carry a per-index derivative witness.
    pub has_derivative_uniform_limit: NameId,
    // --- `CReal.pi` (creal/pi.rs) --------------------------------------------
    /// `creal/pi.rs`'s own 14 names, moved out of this struct by
    /// ADR-1512 so that adding a declaration to that module touches
    /// that module alone.
    ///
    /// Reached as `p.pi.pi.pi_half_coef` and documented in
    /// [`PiNames`] rather than here. No other `creal` module reads
    /// these names, which is what makes the move local rather than a
    /// cross-module rename (`scripts/creal-declare-deps.py`).
    pub pi: PiNames,
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
    let uniformly_continuous_on = kernel.name_str(creal, "UniformlyContinuousOn");
    let uniform_converges_on = kernel.name_str(creal, "UniformConvergesOn");
    let has_derivative_on = kernel.name_str(creal, "HasDerivativeOn");
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
        mul_self_abs: kernel.name_str(creal, "mul_self_abs"),
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
        inv_nonneg: kernel.name_str(creal, "inv_nonneg"),
        le_of_mul_le_mul_left: kernel.name_str(creal, "le_of_mul_le_mul_left"),
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
        min_mono_left: kernel.name_str(creal, "min_mono_left"),
        max_mono_right: kernel.name_str(creal, "max_mono_right"),
        clamp_mono: kernel.name_str(creal, "clamp_mono"),
        clamp_id: kernel.name_str(creal, "clamp_id"),
        max_sub_min: kernel.name_str(creal, "max_sub_min"),
        abs_congr: kernel.name_str(creal, "abs_congr"),
        le_abs_self: kernel.name_str(creal, "le_abs_self"),
        neg_le_abs: kernel.name_str(creal, "neg_le_abs"),
        abs_le: kernel.name_str(creal, "abs_le"),
        abs_add_le: kernel.name_str(creal, "abs_add_le"),
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
        completeness: completeness::CompletenessNames::intern(kernel, creal),
        converges: kernel.name_str(creal, "Converges"),
        converges_unique: kernel.name_str(creal, "converges_unique"),
        converges_of_close: kernel.name_str(creal, "converges_of_close"),
        converges_of_const: kernel.name_str(creal, "converges_of_const"),
        converges_of_equiv: kernel.name_str(creal, "converges_of_equiv"),
        cauchy: kernel.name_str(creal, "Cauchy"),
        converges_cauchy: kernel.name_str(creal, "converges_cauchy"),
        converges_add: kernel.name_str(creal, "converges_add"),
        converges_neg: kernel.name_str(creal, "converges_neg"),
        converges_sub: kernel.name_str(creal, "converges_sub"),
        converges_squeeze: kernel.name_str(creal, "converges_squeeze"),
        converges_lower_bound: kernel.name_str(creal, "converges_lower_bound"),
        converges_lower_bound_shift: kernel.name_str(creal, "converges_lower_bound_shift"),
        converges_upper_bound: kernel.name_str(creal, "converges_upper_bound"),
        cos_sign: cos_sign::CosSignNames::intern(kernel, creal),
        converges_le: kernel.name_str(creal, "converges_le"),
        bounded: kernel.name_str(creal, "Bounded"),
        converges_bounded: kernel.name_str(creal, "converges_bounded"),
        converges_mul: kernel.name_str(creal, "converges_mul"),
        continuous_at: kernel.name_str(creal, "ContinuousAt"),
        continuous_id: kernel.name_str(creal, "continuous_id"),
        continuous_const: kernel.name_str(creal, "continuous_const"),
        continuous_add: kernel.name_str(creal, "continuous_add"),
        continuous_mul: kernel.name_str(creal, "continuous_mul"),
        continuous_comp: kernel.name_str(creal, "continuous_comp"),
        converges_comp_eventually: kernel.name_str(creal, "converges_comp_eventually"),
        uniformly_continuous_on,
        uc_mk: kernel.name_str(uniformly_continuous_on, "mk"),
        uc_rec: kernel.name_str(uniformly_continuous_on, "rec"),
        uc_modulus: kernel.name_str(uniformly_continuous_on, "modulus"),
        uc_spec: kernel.name_str(uniformly_continuous_on, "spec"),
        uniformly_continuous_on_restrict: kernel.name_str(creal, "uniformlyContinuousOn_restrict"),
        uniformly_continuous_id: kernel.name_str(creal, "uniformly_continuous_id"),
        uniformly_continuous_const: kernel.name_str(creal, "uniformly_continuous_const"),
        uniformly_continuous_add: kernel.name_str(creal, "uniformly_continuous_add"),
        uniformly_continuous_neg: kernel.name_str(creal, "uniformly_continuous_neg"),
        uniformly_continuous_sub: kernel.name_str(creal, "uniformly_continuous_sub"),
        uniformly_continuous_mul: kernel.name_str(creal, "uniformly_continuous_mul"),
        uniformly_continuous_sq: kernel.name_str(creal, "uniformly_continuous_sq"),
        bounded_on_id_unit: kernel.name_str(creal, "bounded_on_id_unit"),
        bounded_on_id_zero_one: kernel.name_str(creal, "bounded_on_id_zero_one"),
        uniformly_continuous_poly_example: kernel
            .name_str(creal, "uniformly_continuous_poly_example"),
        mag_bound_le_sum_range_of_lt: kernel.name_str(creal, "mag_bound_le_sumRange_of_lt"),
        bucket_index: kernel.name_str(creal, "bucketIndex"),
        bucket_index_floor_lower: kernel.name_str(creal, "bucketIndexFloorLower"),
        bucket_index_floor_upper: kernel.name_str(creal, "bucketIndexFloorUpper"),
        bucket_clamp_upper: kernel.name_str(creal, "bucketClampUpper"),
        bucket_clamp_lower: kernel.name_str(creal, "bucketClampLower"),
        bucket_index_bound: kernel.name_str(creal, "bucketIndexBound"),
        crossing: crossing::CrossingNames::intern(kernel, creal),
        sample_upper_bound: kernel.name_str(creal, "sampleUpperBound"),
        sample_lower_bound: kernel.name_str(creal, "sampleLowerBound"),
        bucket_close: kernel.name_str(creal, "bucketClose"),
        abs_bound_of_self: kernel.name_str(creal, "abs_bound_of_self"),
        bounded_of_uniformly_continuous: kernel.name_str(creal, "bounded_of_uniformly_continuous"),
        rat_sq_le: kernel.name_str(creal, "ratSqLe"),
        rat_sq_sandwich: kernel.name_str(creal, "ratSqSandwich"),
        rat_index_ratio_le_one: kernel.name_str(creal, "ratIndexRatioLeOne"),
        rat_unit_eq_one: kernel.name_str(creal, "ratUnitEqOne"),
        eq_zero_of_mul_self_zero: kernel.name_str(creal, "eq_zero_of_mul_self_zero"),
        eq_zero_of_add_eq_zero_of_nonneg: kernel
            .name_str(creal, "eq_zero_of_add_eq_zero_of_nonneg"),
        le_of_forall_le_add_small: kernel.name_str(creal, "le_of_forall_le_add_small"),
        equiv_zero_of_small: kernel.name_str(creal, "equiv_zero_of_small"),
        le_of_forall_le_add_rate: kernel.name_str(creal, "le_of_forall_le_add_rate"),
        equiv_zero_of_rate: kernel.name_str(creal, "equiv_zero_of_rate"),
        nat_sqrt: kernel.name_str(creal, "natSqrt"),
        nat_sqrt_spec: kernel.name_str(creal, "natSqrtSpec"),
        nat_sqrt_le: kernel.name_str(creal, "natSqrtLe"),
        nat_sqrt_lt: kernel.name_str(creal, "natSqrtLt"),
        sqrt_approx: kernel.name_str(creal, "sqrtApprox"),
        sqrt_approx_sq_bracket: kernel.name_str(creal, "sqrtApproxSqBracket"),
        sqrt_approx_kregular: kernel.name_str(creal, "sqrtApproxKRegular"),
        sqrt: kernel.name_str(creal, "sqrt"),
        sqrt_congr: kernel.name_str(creal, "sqrt_congr"),
        sqrt_one: kernel.name_str(creal, "sqrt_one"),
        sqrt_zero: kernel.name_str(creal, "sqrt_zero"),
        sqrt_le_sqrt: kernel.name_str(creal, "sqrt_le_sqrt"),
        sqrt_sq: kernel.name_str(creal, "sqrt_sq"),
        sqrt_nonneg: kernel.name_str(creal, "sqrt_nonneg"),
        mul_self_sqrt: kernel.name_str(creal, "mul_self_sqrt"),
        sqrt_mul: kernel.name_str(creal, "sqrt_mul"),
        le_of_sq_le: kernel.name_str(creal, "le_of_sq_le"),
        k_regular_pred: kernel.name_str(creal, "KRegular"),
        speedup: kernel.name_str(creal, "speedup"),
        regular_of_kregular: kernel.name_str(creal, "regular_of_kregular"),
        speedup_close: kernel.name_str(creal, "speedup_close"),
        regular_of_scaled_cauchy: kernel.name_str(creal, "regular_of_scaled_cauchy"),
        converges_of_scaled_cauchy: kernel.name_str(creal, "converges_of_scaled_cauchy"),
        converges_of_cauchy: kernel.name_str(creal, "converges_of_cauchy"),
        sum_range: kernel.name_str(creal, "sumRange"),
        sum_range_zero: kernel.name_str(creal, "sumRange_zero"),
        sum_range_succ: kernel.name_str(creal, "sumRange_succ"),
        sum_range_congr: kernel.name_str(creal, "sumRange_congr"),
        sum_range_add: kernel.name_str(creal, "sumRange_add"),
        mul_sum_range: kernel.name_str(creal, "mul_sumRange"),
        sum_range_le: kernel.name_str(creal, "sumRange_le"),
        abs_sum_range_le: kernel.name_str(creal, "abs_sumRange_le"),
        mono_of_le_succ: kernel.name_str(creal, "monotone_of_le_succ"),
        sum_range_mono_outer: kernel.name_str(creal, "sumRange_mono_outer"),
        sum_range_telescope: kernel.name_str(creal, "sumRange_telescope"),
        sum_range_split: kernel.name_str(creal, "sumRange_split"),
        sum_range_telescope_ge: kernel.name_str(creal, "sumRange_telescope_ge"),
        sum_range_telescope_le: kernel.name_str(creal, "sumRange_telescope_le"),
        sum_range_tail_le: kernel.name_str(creal, "sumRange_tail_le"),
        sum_range_tail_within: kernel.name_str(creal, "sumRange_tail_within"),
        sum_range_tail_within_le: kernel.name_str(creal, "sumRange_tail_within_le"),
        sum_range_tail_cauchy_within: kernel.name_str(creal, "sumRange_tail_cauchy_within"),
        sum_range_tail_within_cauchy: kernel.name_str(creal, "sumRange_tail_within_cauchy"),
        sum_range_cauchy_dominated_ordered: kernel
            .name_str(creal, "sumRange_cauchy_dominated_ordered"),
        sum_range_cauchy_dominated_ordered_normalized: kernel
            .name_str(creal, "sumRange_cauchy_dominated_ordered_normalized"),
        sum_range_cauchy_of_dominated: kernel.name_str(creal, "sumRange_cauchy_of_dominated"),
        sum_range_converges_of_dominated: kernel.name_str(creal, "sumRange_converges_of_dominated"),
        sum_range_comparison_test: kernel.name_str(creal, "sumRange_comparisonTest"),
        sum_range_cauchy_of_abs_cauchy: kernel.name_str(creal, "sumRange_cauchy_of_abs_cauchy"),
        sum_range_converges_of_abs_converges: kernel
            .name_str(creal, "sumRange_converges_of_abs_converges"),
        sum_range_seq_zero: kernel.name_str(creal, "sumRange_seq_zero"),
        sum_range_seq_succ: kernel.name_str(creal, "sumRange_seq_succ"),
        pow: kernel.name_str(creal, "pow"),
        pow_zero: kernel.name_str(creal, "pow_zero"),
        pow_succ: kernel.name_str(creal, "pow_succ"),
        pow_add: kernel.name_str(creal, "pow_add"),
        pow_congr: kernel.name_str(creal, "pow_congr"),
        pow_nonneg: kernel.name_str(creal, "pow_nonneg"),
        pow_le_one: kernel.name_str(creal, "pow_le_one"),
        mul_sub_one_geom: kernel.name_str(creal, "mul_sub_one_geom"),
        geom_sum_bounded: kernel.name_str(creal, "geom_sum_bounded"),
        pow_le_pow_of_le_one: kernel.name_str(creal, "pow_le_pow_of_le_one"),
        mul_sub_one_geom_tail: kernel.name_str(creal, "mul_sub_one_geom_tail"),
        geom_tail_bounded: kernel.name_str(creal, "geom_tail_bounded"),
        geom_tail_bounded_div: kernel.name_str(creal, "geom_tail_bounded_div"),
        geom_tail_within: kernel.name_str(creal, "geom_tail_within"),
        geom_tail_within_le: kernel.name_str(creal, "geom_tail_within_le"),
        geom_pair_within: kernel.name_str(creal, "geom_pair_within"),
        pow_le_pow_of_base_le: kernel.name_str(creal, "pow_le_pow_of_base_le"),
        of_rat_pow: kernel.name_str(creal, "ofRat_pow"),
        pow_half_le_nat_div_succ: kernel.name_str(creal, "pow_half_le_natDivSucc"),
        pow_le_nat_div_succ_of_lt: kernel.name_str(creal, "pow_le_natDivSucc_of_lt"),
        pow_le_nat_div_succ_of_gap: kernel.name_str(creal, "pow_le_natDivSucc_of_gap"),
        ratio_decay_bound: kernel.name_str(creal, "ratioDecayBound"),
        inv_le_of_pos_bound: kernel.name_str(creal, "invLeOfPosBound"),
        geom_y_bound: kernel.name_str(creal, "geomYBound"),
        geom_y_bound_raw: kernel.name_str(creal, "geomYBoundRaw"),
        geom_half_inv_leaf_bound: kernel.name_str(creal, "geomHalfInvLeafBound"),
        geom_cauchy_ordered_half: kernel.name_str(creal, "geomCauchyOrderedHalf"),
        geom_cauchy: kernel.name_str(creal, "geomCauchy"),
        geom_cauchy_of_lt_ordered: kernel.name_str(creal, "geomCauchyOfLtOrdered"),
        geom_cauchy_ordered_of_gap: kernel.name_str(creal, "geomCauchyOrderedOfGap"),
        geom_cauchy_ordered_16_over_25: kernel.name_str(creal, "geomCauchyOrdered16Over25"),
        geom_cauchy_body_of_gap: kernel.name_str(creal, "geomCauchyBodyOfGap"),
        geom_cauchy_body_16_over_25: kernel.name_str(creal, "geomCauchyBody16Over25"),
        geom_cauchy_of_lt: kernel.name_str(creal, "geomCauchyOfLt"),
        ratio_test: ratio_test::RatioTestNames::intern(kernel, creal),
        one_le_pow_of_one_le: kernel.name_str(creal, "one_le_pow_of_one_le"),
        pow_le_pow_of_one_le: kernel.name_str(creal, "pow_le_pow_of_one_le"),
        pow_pos: kernel.name_str(creal, "pow_pos"),
        pow_succ_lt_one: kernel.name_str(creal, "pow_succ_lt_one"),
        pow_succ_gt_one: kernel.name_str(creal, "pow_succ_gt_one"),
        not_apart_one_of_pow_succ_eq_one: kernel
            .name_str(creal, "not_apart_one_of_pow_succ_eq_one"),
        has_derivative_on,
        hd_mk: kernel.name_str(has_derivative_on, "mk"),
        hd_rec: kernel.name_str(has_derivative_on, "rec"),
        hd_modulus: kernel.name_str(has_derivative_on, "modulus"),
        hd_spec: kernel.name_str(has_derivative_on, "spec"),
        has_derivative_const: kernel.name_str(creal, "hasDerivative_const"),
        has_derivative_id: kernel.name_str(creal, "hasDerivative_id"),
        has_derivative_sq: kernel.name_str(creal, "hasDerivative_sq"),
        has_derivative_neg: kernel.name_str(creal, "hasDerivative_neg"),
        has_derivative_add: kernel.name_str(creal, "hasDerivative_add"),
        abs_mul_le_of_bounds: kernel.name_str(creal, "abs_mul_le_of_bounds"),
        bounded_on: kernel.name_str(creal, "BoundedOn"),
        bounded_on_unfold: kernel.name_str(creal, "bounded_on_unfold"),
        bounded_on_mul: kernel.name_str(creal, "bounded_on_mul"),
        bounded_on_add: kernel.name_str(creal, "bounded_on_add"),
        has_derivative_smul: kernel.name_str(creal, "hasDerivative_smul"),
        has_derivative_sub: kernel.name_str(creal, "hasDerivative_sub"),
        has_derivative_mul: kernel.name_str(creal, "hasDerivative_mul"),
        has_derivative_congr: kernel.name_str(creal, "hasDerivative_congr"),
        has_derivative_pow_two: kernel.name_str(creal, "hasDerivative_pow_two"),
        has_derivative_cube: kernel.name_str(creal, "hasDerivative_cube"),
        has_derivative_pow: kernel.name_str(creal, "hasDerivative_pow"),
        has_derivative_chain: kernel.name_str(creal, "hasDerivative_chain"),
        has_derivative_chain_id_sq: kernel.name_str(creal, "hasDerivative_chain_id_sq"),
        riemann_sum: kernel.name_str(creal, "riemannSum"),
        riemann_sum_add: kernel.name_str(creal, "riemannSum_add"),
        mul_riemann_sum: kernel.name_str(creal, "mul_riemannSum"),
        riemann_sum_le: kernel.name_str(creal, "riemannSum_le"),
        riemann_sum_const: kernel.name_str(creal, "riemannSum_const"),
        of_nat_le: kernel.name_str(creal, "ofNat_le"),
        riemann_sample_in_bounds: kernel.name_str(creal, "riemannSum_sample_in_bounds"),
        riemann_sum_le_on: kernel.name_str(creal, "riemannSum_le_on"),
        sum_range_reblock: kernel.name_str(creal, "sumRange_reblock"),
        within_of_two_sided_le: kernel.name_str(creal, "within_of_two_sided_le"),
        le_add_of_abs_sub_le: kernel.name_str(creal, "le_add_of_abs_sub_le"),
        two_sided_of_abs_sub_le: kernel.name_str(creal, "two_sided_of_abs_sub_le"),
        fine_block_sum_close: kernel.name_str(creal, "fineBlockSum_close"),
        has_derivative_close_of_equiv: kernel.name_str(creal, "hasDerivative_closeOfEquiv"),
        exp_term: kernel.name_str(creal, "expTerm"),
        exp_series_partial: kernel.name_str(creal, "expSeriesPartial"),
        exp_term_le_geom: kernel.name_str(creal, "expTerm_le_geom"),
        exp_dominant: kernel.name_str(creal, "expDominant"),
        exp_term_le_dominant: kernel.name_str(creal, "exp_term_le_dominant"),
        exp_term_nonneg: kernel.name_str(creal, "exp_term_nonneg"),
        exp_dominant_nonneg: kernel.name_str(creal, "exp_dominant_nonneg"),
        exp_term_abs_le_dominant: kernel.name_str(creal, "exp_term_abs_le_dominant"),
        sum_pow_half_closed_form: kernel.name_str(creal, "sumRange_pow_half_closed_form"),
        cauchy_of_pointwise_equiv: kernel.name_str(creal, "cauchyOfPointwiseEquiv"),
        exp_dominant_cauchy: kernel.name_str(creal, "expDominantCauchy"),
        exp_series_partial_converges: kernel.name_str(creal, "expSeriesPartialConverges"),
        e: kernel.name_str(creal, "e"),
        e_converges: kernel.name_str(creal, "e_converges"),
        two_le_e: kernel.name_str(creal, "two_le_e"),
        e_le_four: kernel.name_str(creal, "e_le_four"),
        e_le_three: kernel.name_str(creal, "e_le_three"),
        cos_term: kernel.name_str(creal, "cosTerm"),
        cos_series_partial: kernel.name_str(creal, "cosSeriesPartial"),
        cos_term_abs_le_dominant: kernel.name_str(creal, "cosTermAbsLeDominant"),
        cos_one: kernel.name_str(creal, "cosOne"),
        cos_one_converges: kernel.name_str(creal, "cosOneConverges"),
        cos_one_le_four: kernel.name_str(creal, "cosOne_le_four"),
        neg_four_le_cos_one: kernel.name_str(creal, "neg_four_le_cosOne"),
        exp_term_antitone: kernel.name_str(creal, "expTerm_antitone"),
        cos_one_alternating_lower: kernel.name_str(creal, "cosOne_alternating_lower"),
        cos_one_alternating_upper: kernel.name_str(creal, "cosOne_alternating_upper"),
        cos_one_nonneg: kernel.name_str(creal, "cosOne_nonneg"),
        cos_one_le_exp_term_zero: kernel.name_str(creal, "cosOne_le_exp_term_zero"),
        neg_one_pow_double: kernel.name_str(creal, "negOnePowDouble"),
        alternating_e_le_o: kernel.name_str(creal, "alternatingELeO"),
        alternating_bracket: kernel.name_str(creal, "alternatingBracket"),
        alternating_bracket_upper: kernel.name_str(creal, "alternatingBracketUpper"),
        alternating_lower_bound: kernel.name_str(creal, "alternatingLowerBound"),
        alternating_upper_bound: kernel.name_str(creal, "alternatingUpperBound"),
        sum_range_const: kernel.name_str(creal, "sumRange_const"),
        mesh_count_width: kernel.name_str(creal, "mesh_count_width"),
        subdivision_point_in_bounds: kernel.name_str(creal, "subdivisionPoint_in_bounds"),
        sum_range_double: kernel.name_str(creal, "sumRange_double"),
        of_nat_add: kernel.name_str(creal, "ofNat_add"),
        of_nat_mul: kernel.name_str(creal, "ofNat_mul"),
        monotone_of_nonneg_deriv: kernel.name_str(creal, "monotone_of_nonneg_deriv"),
        strict_mono_of_pos_deriv: kernel.name_str(creal, "strict_mono_of_pos_deriv"),
        strict_mono_magnitude: kernel.name_str(creal, "strict_mono_magnitude"),
        scale_cancel_le: kernel.name_str(creal, "scale_cancel_le"),
        diff_le_of_strict_mono_magnitude: kernel
            .name_str(creal, "diff_le_of_strict_mono_magnitude"),
        strict_injective_of_pos_deriv: kernel.name_str(creal, "strict_injective_of_pos_deriv"),
        inverse_fn: inverse_fn::InverseFnNames::intern(kernel, creal),
        inverse_lipschitz_of_pos_deriv: kernel.name_str(creal, "inverse_lipschitz_of_pos_deriv"),
        ivt_step: kernel.name_str(creal, "ivt_step"),
        constant_of_zero_deriv: kernel.name_str(creal, "constant_of_zero_deriv"),
        antitone_of_nonpos_deriv: kernel.name_str(creal, "antitone_of_nonpos_deriv"),
        strict_antitone_of_neg_deriv: kernel.name_str(creal, "strict_antitone_of_neg_deriv"),
        strict_mono_comp: kernel.name_str(creal, "strict_mono_comp"),
        ivt_iter: kernel.name_str(creal, "ivt_iter"),
        ivt_approx: kernel.name_str(creal, "ivt_approx"),
        ivt_bisect: kernel.name_str(creal, "ivt_bisect"),
        ivt_bisect_lo: kernel.name_str(creal, "ivt_bisect_lo"),
        ivt_bisect_hi: kernel.name_str(creal, "ivt_bisect_hi"),
        ivt_bisect_invariant: kernel.name_str(creal, "ivt_bisect_invariant"),
        ivt_bisect_diag: kernel.name_str(creal, "ivt_bisect_diag"),
        ivt_bisect_diag_lo: kernel.name_str(creal, "ivt_bisect_diag_lo"),
        ivt_bisect_diag_hi: kernel.name_str(creal, "ivt_bisect_diag_hi"),
        ivt_bisect_approx: kernel.name_str(creal, "ivt_bisect_approx"),
        abs_diff_le_of_small_image: kernel.name_str(creal, "abs_diff_le_of_small_image"),
        ivt_bisect_cauchy_bound: kernel.name_str(creal, "ivt_bisect_cauchy_bound"),
        cauchy_of_abs_diff_le: kernel.name_str(creal, "cauchy_of_abs_diff_le"),
        scaled_cauchy_of_abs_diff_le: kernel.name_str(creal, "scaledCauchy_of_abs_diff_le"),
        converges_of_abs_diff_le: kernel.name_str(creal, "converges_of_abs_diff_le"),
        ivt_bisect_cauchy: kernel.name_str(creal, "ivt_bisect_cauchy"),
        ivt_exact_root: kernel.name_str(creal, "ivt_exact_root"),
        deriv_unique: deriv_unique::DerivUniqueNames::intern(kernel, creal),
        fermat_interior_extremum: kernel.name_str(creal, "fermat_interiorExtremum"),
        rolle_interior_extremum: kernel.name_str(creal, "rolle_interiorExtremum"),
        mvt: mvt::MvtNames::intern(kernel, creal),
        mesh_le_of_ge: kernel.name_str(creal, "mesh_le_of_ge"),
        mesh_scaled_le_of_ge: kernel.name_str(creal, "meshScaledLeOfGe"),
        fine_sample_in_bounds: kernel.name_str(creal, "fineSample_in_bounds"),
        fine_sample_close: kernel.name_str(creal, "fineSample_close"),
        mesh_reciprocal_mul: kernel.name_str(creal, "meshReciprocalMul"),
        equiv_abs_diff_le: kernel.name_str(creal, "equivAbsDiffLe"),
        sample_point_reblock: kernel.name_str(creal, "samplePoint_reblock"),
        reblock_block_eq_fine_block_sum: kernel.name_str(creal, "reblockBlock_eq_fineBlockSum"),
        riemann_sum_reblock_close: kernel.name_str(creal, "riemannSum_reblock_close"),
        riemann_sum_cauchy: kernel.name_str(creal, "riemannSum_cauchy"),
        shared_index_to_canonical: kernel.name_str(creal, "sharedIndexToCanonical"),
        riemann_sum_shared_accuracy_close: kernel.name_str(creal, "riemannSum_sharedAccuracyClose"),
        riemann_sum_shared_accuracy_close_at: kernel
            .name_str(creal, "riemannSum_sharedAccuracyClose_at"),
        riemann_sum_total_eps_le: kernel.name_str(creal, "riemannSumTotalEpsLe"),
        riemann_sum_deep_cauchy: kernel.name_str(creal, "riemannSumDeepCauchy"),
        riemann_sum_deep_cauchy_folded: kernel.name_str(creal, "riemannSumDeepCauchyFolded"),
        riemann_sum_deep_cauchy_cross: kernel.name_str(creal, "riemannSumDeepCauchyCross"),
        riemann_sum_deep_cauchy_cross_folded: kernel
            .name_str(creal, "riemannSumDeepCauchyCrossFolded"),
        riemann_sum_add_cauchy_cross: kernel.name_str(creal, "riemannSumAddCauchyCross"),
        integral: kernel.name_str(creal, "integral"),
        integral_converges: kernel.name_str(creal, "integral_converges"),
        integral_const: kernel.name_str(creal, "integral_const"),
        integral_witness_independent: kernel.name_str(creal, "integral_witness_independent"),
        integral_add: kernel.name_str(creal, "integral_add"),
        integral_le: kernel.name_str(creal, "integral_le"),
        integral_split: kernel.name_str(creal, "integral_split"),
        split_point_approx: kernel.name_str(creal, "splitPointApprox"),
        integral_endpoint_close: kernel.name_str(creal, "integralEndpointClose"),
        integral_split_arbitrary: kernel.name_str(creal, "integralSplitArbitrary"),
        integral_split_anywhere: kernel.name_str(creal, "integralSplitAnywhere"),
        has_derivative_antiderivative: kernel.name_str(creal, "hasDerivative_antiderivative"),
        integral_eq_antideriv_diff: kernel.name_str(creal, "integral_eq_antideriv_diff"),
        integral_by_parts: kernel.name_str(creal, "integral_by_parts"),
        integral_abs_le: kernel.name_str(creal, "integral_abs_le"),
        integral_abs_le_of_bound: kernel.name_str(creal, "integral_abs_le_of_bound"),
        integral_sub_linear_le: kernel.name_str(creal, "integral_sub_linear_le"),
        antiderivative: kernel.name_str(creal, "antiderivative"),
        antiderivative_abs_le: kernel.name_str(creal, "antiderivative_abs_le"),
        integral_scale: kernel.name_str(creal, "integral_scale"),
        riemann_sum_integral_close: kernel.name_str(creal, "riemannSum_integral_close"),
        riemann_sum_split_exact: kernel.name_str(creal, "riemannSum_split_exact"),
        riemann_sum_split_scale_invariant: kernel
            .name_str(creal, "riemannSum_split_scale_invariant"),
        congr_of_uniformly_continuous: kernel.name_str(creal, "congrOfUniformlyContinuous"),
        riemann_sum_split_exact_of_uc: kernel.name_str(creal, "riemannSum_split_exact_of_uc"),
        has_derivative_integral_const: kernel.name_str(creal, "hasDerivative_integral_const"),
        neg_sub_swap: kernel.name_str(creal, "neg_sub_swap"),
        abs_le_of_two_sided: kernel.name_str(creal, "abs_le_of_two_sided"),
        uniform_converges_on,
        uconv_mk: kernel.name_str(uniform_converges_on, "mk"),
        uconv_rec: kernel.name_str(uniform_converges_on, "rec"),
        uconv_rate: kernel.name_str(uniform_converges_on, "rate"),
        uconv_spec: kernel.name_str(uniform_converges_on, "spec"),
        uniform_converges_id: kernel.name_str(creal, "uniform_converges_id"),
        uniform_converges_geom_half: kernel.name_str(creal, "uniform_converges_geom_half"),
        uniform_limit_uniformly_continuous: kernel
            .name_str(creal, "uniform_limit_uniformly_continuous"),
        polynomial: polynomial::PolynomialNames::intern(kernel, creal),
        uniform_converges_add: kernel.name_str(creal, "uniform_converges_add"),
        close_within_of_within: kernel.name_str(creal, "close_within_of_within"),
        close_within_of_within_indexed: kernel.name_str(creal, "close_within_of_within_indexed"),
        weierstrass_m_test: kernel.name_str(creal, "weierstrassMTest"),
        power_series_term: kernel.name_str(creal, "powerSeriesTerm"),
        power_series_term_congr: kernel.name_str(creal, "powerSeriesTerm_congr"),
        power_series_term_abs_le: kernel.name_str(creal, "powerSeriesTerm_abs_le"),
        power_series_uniform_converges: kernel.name_str(creal, "powerSeriesUniformConvergesOn"),
        sin_term: kernel.name_str(creal, "sinTerm"),
        sin_series_partial: kernel.name_str(creal, "sinSeriesPartial"),
        sin_term_abs_le_dominant: kernel.name_str(creal, "sinTermAbsLeDominant"),
        sin_one: kernel.name_str(creal, "sinOne"),
        sin_one_converges: kernel.name_str(creal, "sinOneConverges"),
        sin_one_alternating_lower: kernel.name_str(creal, "sinOne_alternating_lower"),
        sin_one_alternating_upper: kernel.name_str(creal, "sinOne_alternating_upper"),
        sin_one_nonneg: kernel.name_str(creal, "sinOne_nonneg"),
        sin_one_le_exp_term_one: kernel.name_str(creal, "sinOne_le_exp_term_one"),
        exp_term_zero_eq_one: kernel.name_str(creal, "expTerm_zero_eq_one"),
        exp_term_one_eq_one: kernel.name_str(creal, "expTerm_one_eq_one"),
        mul_pow_congr: kernel.name_str(creal, "mulPowCongr"),
        extreme_value: extreme_value::ExtremeValueNames::intern(kernel, creal),
        ivt_boundary: ivt_boundary::IvtBoundaryNames::intern(kernel, creal),
        lub_boundary: lub_boundary::LubBoundaryNames::intern(kernel, creal),
        cos_fn_term: kernel.name_str(creal, "cosFnTerm"),
        cos_fn_term_abs_le: kernel.name_str(creal, "cosFnTermAbsLe"),
        cos_fn_term_congr: kernel.name_str(creal, "cosFnTerm_congr"),
        cos_fn: kernel.name_str(creal, "cosFn"),
        cos_fn_uniform_converges: kernel.name_str(creal, "cosFnUniformConverges"),
        cos_fn_term_abs_le_wide: kernel.name_str(creal, "cosFnTermAbsLeWide"),
        cos_dominant_16_over_25: kernel.name_str(creal, "cosDominant16Over25"),
        cos_dominant_16_over_25_cauchy_body: kernel
            .name_str(creal, "cosDominant16Over25CauchyBody"),
        pow_mul_distrib: kernel.name_str(creal, "powMulDistrib"),
        cos_fn_wide: kernel.name_str(creal, "cosFnWide"),
        cos_fn_wide_uniform_converges: kernel.name_str(creal, "cosFnWideUniformConverges"),
        cos_fn_one_equiv_cos_one: kernel.name_str(creal, "cosFn_one_equiv_cosOne"),
        cos_fn_wide_uniformly_continuous: kernel.name_str(creal, "cosFnWideUniformlyContinuous"),
        cos_fn_wide_one_equiv_cos_one: kernel.name_str(creal, "cosFnWide_one_equiv_cosOne"),
        cos_fn_wide_one_nonneg: kernel.name_str(creal, "cosFnWide_one_nonneg"),
        has_derivative_on_restrict: kernel.name_str(creal, "hasDerivativeOn_restrict"),
        sin_fn_term: kernel.name_str(creal, "sinFnTerm"),
        sin_fn_term_congr: kernel.name_str(creal, "sinFnTerm_congr"),
        sin_fn_term_abs_le_wide: kernel.name_str(creal, "sinFnTermAbsLeWide"),
        sin_dominant_16_over_25: kernel.name_str(creal, "sinDominant16Over25"),
        sin_dominant_16_over_25_cauchy_body: kernel
            .name_str(creal, "sinDominant16Over25CauchyBody"),
        sin_fn: kernel.name_str(creal, "sinFn"),
        sin_fn_uniform_converges: kernel.name_str(creal, "sinFnUniformConverges"),
        sin_fn_uniformly_continuous: kernel.name_str(creal, "sinFnUniformlyContinuous"),
        sin_fn_lower_bound_one_to_r: kernel.name_str(creal, "sinFnLowerBoundOneToR"),
        exp_term_succ_scale: kernel.name_str(creal, "expTermSuccScale"),
        cos_fn_term_deriv_coeff: kernel.name_str(creal, "cosFnTermDerivCoeff"),
        cos_fn_term_has_derivative: kernel.name_str(creal, "cosFnTermHasDerivative"),
        cos_fn_partial_has_derivative: kernel.name_str(creal, "cosFnPartialHasDerivative"),
        nat_div_succ_step_le: kernel.name_str(creal, "natDivSuccStepLe"),
        uniform_converges_shift: kernel.name_str(creal, "uniformConvergesShift"),
        uniform_converges_neg: kernel.name_str(creal, "uniformConvergesNeg"),
        cos_fn_wide_has_derivative: kernel.name_str(creal, "cosFnWideHasDerivative"),
        exp_fn: exp_fn::ExpFnNames::intern(kernel, creal),
        max_range: kernel.name_str(creal, "maxRange"),
        max_range_zero: kernel.name_str(creal, "maxRange_zero"),
        max_range_succ: kernel.name_str(creal, "maxRange_succ"),
        max_range_self_le: kernel.name_str(creal, "maxRange_self_le"),
        max_range_mono: kernel.name_str(creal, "maxRange_mono"),
        max_range_ub: kernel.name_str(creal, "maxRange_ub"),
        max_range_transport: kernel.name_str(creal, "maxRange_transport"),
        mesh_level_count: kernel.name_str(creal, "meshLevelCount"),
        mesh_level_count_zero: kernel.name_str(creal, "meshLevelCount_zero"),
        mesh_level_count_succ: kernel.name_str(creal, "meshLevelCount_succ"),
        mesh_level_count_pow: kernel.name_str(creal, "meshLevelCount_pow"),
        mesh_level_count_ge_of_size: kernel.name_str(creal, "meshLevelCount_ge_of_size"),
        mesh_max: kernel.name_str(creal, "meshMax"),
        mesh_max_step_le: kernel.name_str(creal, "meshMax_step_le"),
        mesh_max_mono: kernel.name_str(creal, "meshMax_mono"),
        exp_of_modulus: kernel.name_str(creal, "expOfModulus"),
        true_exp_of_modulus: kernel.name_str(creal, "trueExpOfModulus"),
        true_exp_of_modulus_zero: kernel.name_str(creal, "trueExpOfModulus_zero"),
        true_exp_of_modulus_succ: kernel.name_str(creal, "trueExpOfModulus_succ"),
        true_exp_of_modulus_step_le: kernel.name_str(creal, "trueExpOfModulus_step_le"),
        true_exp_of_modulus_mono: kernel.name_str(creal, "trueExpOfModulus_mono"),
        exp_of_modulus_le_true_exp_of_modulus: kernel
            .name_str(creal, "expOfModulus_le_trueExpOfModulus"),
        mesh_point_near_coarse: kernel.name_str(creal, "meshPoint_near_coarse"),
        max_range_le_add_of_exists: kernel.name_str(creal, "maxRange_le_add_of_exists"),
        mesh_max_le_add_of_step_close: kernel.name_str(creal, "meshMax_le_add_of_step_close"),
        mesh_max_le_add_of_modulus: kernel.name_str(creal, "meshMax_le_add_of_modulus"),
        sup_level: kernel.name_str(creal, "supLevel"),
        sup_level_mono: kernel.name_str(creal, "supLevel_mono"),
        sup_seq: kernel.name_str(creal, "supSeq"),
        sup_seq_mono: kernel.name_str(creal, "supSeq_mono"),
        sup_seq_le_add: kernel.name_str(creal, "supSeq_le_add"),
        le_mesh_level_count: kernel.name_str(creal, "le_meshLevelCount"),
        sup_seq_abs_diff_le: kernel.name_str(creal, "supSeq_abs_diff_le"),
        sup_seq_cauchy: kernel.name_str(creal, "supSeq_cauchy"),
        sup_on: kernel.name_str(creal, "supOn"),
        sup_seq_converges_sup_on: kernel.name_str(creal, "supSeq_converges_supOn"),
        max_range_attained_approx: kernel.name_str(creal, "maxRange_attained_approx"),
        sup_seq_le_shift: kernel.name_str(creal, "supSeq_le_shift"),
        sup_on_approx_lub: kernel.name_str(creal, "supOn_approx_lub"),
        sup_seq_le_sup_on: kernel.name_str(creal, "supSeq_le_supOn"),
        sup_on_ub_at_sup_seq_point: kernel.name_str(creal, "supOn_ub_at_supSeq_point"),
        step_family_locate: kernel.name_str(creal, "stepFamily_locate"),
        mesh_max_le_sup_on_add: kernel.name_str(creal, "meshMax_le_supOn_add"),
        sup_on_ub_at_fine_mesh_point: kernel.name_str(creal, "supOn_ub_at_fine_mesh_point"),
        sup_on_ub: kernel.name_str(creal, "supOn_ub"),
        evt_row1: evt_row1::EvtRow1Names::intern(kernel, creal),
        abs_diff_le_of_deriv_bound: kernel.name_str(creal, "abs_diff_le_of_deriv_bound"),
        lipschitz_of_deriv_bound: kernel.name_str(creal, "lipschitz_of_deriv_bound"),
        abs_diff_sub_le_of_deriv_bound: kernel.name_str(creal, "abs_diff_sub_le_of_deriv_bound"),
        has_derivative_uniform_limit: kernel.name_str(creal, "hasDerivative_uniform_limit"),
        pi: pi::PiNames::intern(kernel, creal),
    }
}

// ---------------------------------------------------------------------------
// Build order as data (level 1 of the phase-order fix)
// ---------------------------------------------------------------------------
//
// `docs/research/11-design-review/2026-08-27-architecture-review.md` §1
// measures the failure class this section exists to eliminate: every
// `CRealPrelude` `NameId` is interned up front by `intern_names`, so `p.foo`
// is always a valid *handle* -- the failure is that the *declaration* `foo`
// is not yet in the kernel environment when a `declare_*` runs, and the
// kernel's `UnknownConst` is indistinguishable from `foo` never having been
// written at all. Four lanes hit exactly this in this file in one day and
// each "fixed" it by adding a duplicate declaration elsewhere, because the
// error gave no way to tell "not yet declared" from "does not exist".
//
// [`BuildStep`] makes each step's dependencies data instead of only being
// implicit in call order, and [`validate_step_order`] checks that data is
// self-consistent -- purely structurally, with no kernel involved -- so a
// step moved earlier than its dependency is caught with a diagnosis naming
// the missing declaration, the step that would produce it, and both steps'
// positions, before the kernel ever sees a malformed term.
//
// This is the same mechanism prototyped on `complex.rs`
// (`docs/research/11-design-review/2026-08-27-prelude-build-spike.md`),
// applied here at the same granularity: one [`BuildStep`] per top-level call
// in the existing `build_creal_prelude_uncached` sequence (a module's own
// internal `declare_*` helpers fold into their module's single dispatch
// entry, exactly as `poly.rs`'s 18 internal calls folded into
// `poly::declare_polynomial` in the prototype). Level 1 only: no
// `CRealPrelude` field moves out of this struct (that is Part B of the
// spike, explicitly out of scope here -- the measured churn for a full
// `creal` module split is ~8,997 call sites across 71 files, vs. the
// prototype's actual 144).

/// One step of [`build_creal_prelude_uncached`]'s build order: the fields
/// (by [`CRealPrelude`] accessor) this step's proof terms reference and
/// therefore require already declared in the kernel environment, the fields
/// it declares once it runs, and the `declare_*` function itself.
///
/// `requires`/`provides` are function pointers rather than string literals so
/// a field rename is a compile error here, not a silently-stale table; the
/// human-readable name used in diagnostics is rendered from the `NameId`
/// itself (`render_name`), which is also what the kernel's own errors name.
struct BuildStep {
    /// The declaring function's name, for diagnostics only.
    label: &'static str,
    /// Fields this step's proof terms reference and so requires already
    /// declared. Extracted from the existing `build_creal_prelude_uncached`
    /// call sequence and each step's referenced fields, transitively through
    /// this module's private term-builder helpers and per-module declaring
    /// helpers (closures/sibling functions taking a `name: NameId`
    /// parameter) -- see
    /// `docs/research/11-design-review/2026-08-27-prelude-build-spike.md`.
    requires: &'static [fn(CRealPrelude) -> NameId],
    /// Fields this step declares (via `add_declaration`/`add_inductive`,
    /// including a declared inductive's kernel-generated recursor).
    provides: &'static [fn(CRealPrelude) -> NameId],
    /// The `declare_*` function that performs the declaration(s).
    run: fn(&mut IntDev<'_>, CRealPrelude) -> Result<(), KernelError>,
}

/// Renders a [`NameId`]'s dotted display form (e.g. `"CReal.mul"`), for
/// diagnostics only. Name *identity* is always `NameId` equality (`name.rs`);
/// this never participates in it.
fn render_name(kernel: &Kernel, name: NameId) -> String {
    match kernel.name_node(name) {
        NameNode::Anonymous => String::new(),
        NameNode::Str(parent, s) => {
            let parent_text = render_name(kernel, *parent);
            if parent_text.is_empty() {
                s.clone()
            } else {
                format!("{parent_text}.{s}")
            }
        }
        NameNode::Num(parent, n) => {
            let parent_text = render_name(kernel, *parent);
            if parent_text.is_empty() {
                n.to_string()
            } else {
                format!("{parent_text}.{n}")
            }
        }
    }
}

/// A [`STEPS`] entry requires a declaration before the step that would
/// produce it has run -- the phase-order failure class from §1 of the
/// architecture review, caught structurally rather than as a raw
/// `UnknownConst`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct OrderViolation {
    /// Index into `steps` of the step whose `requires` fired.
    consumer_index: usize,
    /// That step's label.
    consumer_label: &'static str,
    /// The missing declaration.
    missing: NameId,
    /// The step that declares `missing` and its index, if any step in the
    /// table does. `None` means the table itself is incomplete: it names a
    /// dependency nothing in `steps` provides, which is a bug in the table,
    /// not merely in the order.
    provider: Option<(usize, &'static str)>,
}

/// Checks that `steps` is a valid topological order for the dependencies it
/// declares: every `requires` entry is provided by a strictly earlier step.
///
/// Purely structural: evaluates each step's accessor against `p` to obtain
/// concrete `NameId`s, but never touches a kernel's environment. That is what
/// makes it possible to test with a deliberately-broken order (see
/// `creal_tests::order_violation_is_detected_and_precise`) without building
/// anything, and to run it as a preflight in [`build_creal_prelude_uncached`]
/// before any expensive kernel work.
///
/// # Errors
///
/// The first requirement not satisfied by a strictly earlier step, as an
/// [`OrderViolation`].
///
/// **No longer on the build path.** [`plan_step_order`] computes the order
/// instead of checking a hand-written one, and subsumes this: an order this
/// function rejects is one the planner simply repairs. It is kept as the
/// level-1 reference the level-2 behaviour is stated against -- the pair
/// `order_violation_is_detected_and_precise` /
/// `planned_order_repairs_a_consumer_placed_before_its_provider` is the
/// before/after of one input, and without this function the "after" has
/// nothing to be after.
#[cfg(test)]
fn validate_step_order(p: CRealPrelude, steps: &'static [BuildStep]) -> Result<(), OrderViolation> {
    let mut declared: std::collections::HashSet<NameId> = std::collections::HashSet::new();
    for (index, step) in steps.iter().enumerate() {
        for &req in step.requires {
            let name = req(p);
            if declared.contains(&name) {
                continue;
            }
            let provider = steps
                .iter()
                .enumerate()
                .find(|(_, s)| s.provides.iter().any(|&pf| pf(p) == name))
                .map(|(i, s)| (i, s.label));
            return Err(OrderViolation {
                consumer_index: index,
                consumer_label: step.label,
                missing: name,
                provider,
            });
        }
        for &prov in step.provides {
            declared.insert(prov(p));
        }
    }
    Ok(())
}

/// A `CRealPrelude` field is declared by two different [`STEPS`] entries.
///
/// A step can only provide what it declares, so this is always a bug in the
/// table rather than in the order, and it is the one that made the level-1
/// preflight weaker than it reads. Measured 2026-09-01 by
/// `scripts/creal-declare-deps.py`: `mul_self_zero::declare_mul_self_zero`
/// claimed `p.seq` and `p.shared_index_to_canonical`, and
/// `creal/mul_self_zero.rs` declares neither. The real provider of
/// `CReal.sharedIndexToCanonical` is step 98, so
/// [`validate_step_order`] believed it available from step 50 -- a 48-step
/// window in which a genuine phase-order bug passes the preflight and then
/// fails in the kernel with exactly the `UnknownConst` the preflight exists
/// to replace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DuplicateProvider {
    /// The over-claimed declaration.
    name: NameId,
    /// The first step in the table claiming to provide it.
    first: (usize, &'static str),
    /// The second.
    second: (usize, &'static str),
}

/// Either a table that names two providers for one declaration, or a
/// requirement no ordering can satisfy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PlanError {
    /// Two steps claim the same declaration.
    Duplicate(DuplicateProvider),
    /// A requirement nothing provides, or a dependency cycle.
    Order(OrderViolation),
}

/// Computes the build order from the dependency graph, rather than reading it
/// off `steps`'s array order.
///
/// This is the level-2 fix the architecture review asks for (§1): *"each
/// `declare_*` announces the declarations it depends on; the builder
/// topologically sorts them"*. Level 1 made the dependencies data and checked
/// the hand-written order against them; the order was still hand-maintained,
/// so moving a `BuildStep` in the array was still a way to break the build.
/// Here the array order is only a TIE-BREAK.
///
/// **The tie-break makes this a no-op today, deliberately.** Kahn's algorithm
/// taking the lowest-numbered ready step yields the lexicographically smallest
/// valid topological order, and when the array order is ITSELF valid that is
/// the array order: at position `k` every step `< k` has already run, step `k`
/// has all its dependencies among them and so is ready, and no smaller index
/// remains. So this returns `0..steps.len()` unchanged for the table as it
/// stands (pinned by `creal_tests::planned_order_is_the_array_order_today`)
/// and the kernel sees the identical sequence of `add_declaration` calls.
/// What changes is that a step moved in the array is now moved BACK, instead
/// of aborting the build.
///
/// Purely structural: evaluates each accessor against `p` to obtain concrete
/// `NameId`s and never touches a kernel environment.
///
/// # Errors
///
/// [`PlanError::Duplicate`] if two steps claim one declaration -- unorderable
/// because "the provider of `x`" is then not a function. [`PlanError::Order`]
/// otherwise: a requirement nothing provides (`provider: None`), or a cycle
/// (`provider: Some(..)`, naming a step that cannot be scheduled first).
fn plan_step_order(p: CRealPrelude, steps: &'static [BuildStep]) -> Result<Vec<usize>, PlanError> {
    let mut provider: std::collections::HashMap<NameId, (usize, &'static str)> =
        std::collections::HashMap::new();
    for (index, step) in steps.iter().enumerate() {
        for &prov in step.provides {
            let name = prov(p);
            if let Some(&first) = provider.get(&name) {
                return Err(PlanError::Duplicate(DuplicateProvider {
                    name,
                    first,
                    second: (index, step.label),
                }));
            }
            provider.insert(name, (index, step.label));
        }
    }

    // Edges provider -> consumer, plus each step's count of unmet
    // requirements. A requirement a step provides itself is not an edge.
    let mut consumers: Vec<Vec<usize>> = vec![Vec::new(); steps.len()];
    let mut unmet: Vec<usize> = vec![0; steps.len()];
    for (index, step) in steps.iter().enumerate() {
        for &req in step.requires {
            let name = req(p);
            match provider.get(&name) {
                Some(&(source, _)) if source != index => {
                    consumers[source].push(index);
                    unmet[index] += 1;
                }
                Some(_) => {}
                None => {
                    return Err(PlanError::Order(OrderViolation {
                        consumer_index: index,
                        consumer_label: step.label,
                        missing: name,
                        provider: None,
                    }));
                }
            }
        }
    }

    // Kahn's algorithm with a min-heap on the SOURCE index: deterministic, and
    // equal to the array order whenever the array order is valid.
    let mut ready: std::collections::BinaryHeap<std::cmp::Reverse<usize>> = (0..steps.len())
        .filter(|&index| unmet[index] == 0)
        .map(std::cmp::Reverse)
        .collect();
    let mut plan = Vec::with_capacity(steps.len());
    while let Some(std::cmp::Reverse(index)) = ready.pop() {
        plan.push(index);
        for &consumer in &consumers[index] {
            unmet[consumer] -= 1;
            if unmet[consumer] == 0 {
                ready.push(std::cmp::Reverse(consumer));
            }
        }
    }

    if plan.len() != steps.len() {
        // A cycle. Report the lowest-numbered step still blocked, naming one
        // requirement it is blocked on -- the same shape `validate_step_order`
        // reports, so a caller renders both the same way.
        let stuck = (0..steps.len())
            .find(|&index| unmet[index] > 0)
            .expect("a short plan means at least one step is still blocked");
        let step = &steps[stuck];
        let (missing, blocker) = step
            .requires
            .iter()
            .map(|&req| req(p))
            .find_map(|name| {
                provider
                    .get(&name)
                    .filter(|&&(source, _)| source != stuck && unmet[source] > 0)
                    .map(|&source| (name, source))
            })
            .expect("a blocked step is blocked by a provider that is itself blocked");
        return Err(PlanError::Order(OrderViolation {
            consumer_index: stuck,
            consumer_label: step.label,
            missing,
            provider: Some(blocker),
        }));
    }
    Ok(plan)
}

/// The `creal` prelude's build order, as data: each step names the fields
/// (by [`CRealPrelude`] accessor) it requires already declared in the
/// kernel environment and the fields it declares once it runs.
///
/// This is the level-1 fix for the phase-order failure class in
/// `docs/research/11-design-review/2026-08-27-architecture-review.md` §1:
/// `KernelError::UnknownConst` alone is indistinguishable from "this
/// declaration does not exist", because every `NameId` is interned up
/// front regardless of build order. [`validate_step_order`] checks this
/// table's internal consistency (purely structurally, no kernel needed) so
/// a step moved earlier than its dependency is caught with a diagnostic
/// naming the missing declaration, the step that would produce it, and
/// both steps' positions -- instead of a bare `UnknownConst` indistinguishable
/// from a missing declaration.
///
/// Generated from the existing `build_creal_prelude_uncached` call sequence
/// and each step's referenced `CRealPrelude` fields (transitively, through
/// this module's private term-builder helpers and per-module declaring
/// helpers); see
/// `docs/research/11-design-review/2026-08-27-prelude-build-spike.md` for the
/// extraction method this reuses. Validated: the existing order already
/// satisfies every one of the 2,264 requirement edges below.
/// The `creal` prelude's build ORDER and dispatch, hand-maintained: one entry
/// per top-level call in the `build_creal_prelude_uncached` sequence, naming
/// the step and the `declare_*` that performs it.
///
/// **The dependency data is deliberately not here.** It used to be: each entry
/// carried hand-written `requires`/`provides` accessor lists, and the level-1
/// preflight ([`validate_step_order`]) and the level-2 planner
/// ([`plan_step_order`]) could only constrain the edges those lists named.
/// Measured 2026-09-01 (`scripts/creal-declare-deps.py`), the lists named
/// **3,934 of the 4,831** `requires` edges the code actually has, so 977 edges
/// -- spread over 175 of the 211 steps -- constrained nothing. An inversion on
/// any of them passed the preflight and then failed in the kernel as a bare
/// `UnknownConst`, which is the shape of gate CLAUDE.md calls worse than no
/// gate at all: measured on the parent commit, swapping steps 98 and 100
/// (`integral::declare_shared_index_to_canonical` and its consumer) produced
/// **zero** violations from the hand-written table and one from the measured
/// graph.
///
/// So [`STEPS`] is now GENERATED from this table plus a measurement of the
/// source: `crates/axeyum-lean-kernel/src/creal/steps_generated.rs`, written
/// by `scripts/creal-declare-deps.py` and gated stale by its `--check`.
/// Adding a step means adding one line here and re-running the generator; a
/// dependency edge is never written by hand again.
type StepDispatch = (
    &'static str,
    fn(&mut IntDev<'_>, CRealPrelude) -> Result<(), KernelError>,
);

const STEP_DISPATCH: &[StepDispatch] = &[
    ("declare_predicates", declare_predicates),
    ("declare_carrier", declare_carrier),
    ("declare_projections", declare_projections),
    ("declare_equiv", declare_equiv),
    ("declare_reflexivity", declare_reflexivity),
    ("declare_symmetry", declare_symmetry),
    ("declare_transitivity", declare_transitivity),
    ("declare_of_rat", declare_of_rat),
    ("declare_discrimination", declare_discrimination),
    ("declare_constants", declare_constants),
    ("declare_pointwise", declare_pointwise),
    ("declare_negation", declare_negation),
    ("declare_addition", declare_addition),
    ("declare_additive_laws", declare_additive_laws),
    ("declare_of_rat_add", declare_of_rat_add),
    ("declare_of_rat_neg", declare_of_rat_neg),
    ("declare_of_rat_sub", declare_of_rat_sub),
    ("declare_order", declare_order),
    ("declare_neg_le_neg", declare_neg_le_neg),
    ("declare_strict_order", declare_strict_order),
    (
        "order_extra::declare_order_extra",
        order_extra::declare_order_extra,
    ),
    ("product::declare_product", product::declare_product),
    ("field::declare_field", field::declare_field),
    ("inverse::declare_inverse", inverse::declare_inverse),
    (
        "cancellation::declare_cancellation",
        cancellation::declare_cancellation,
    ),
    ("lattice::declare_lattice", lattice::declare_lattice),
    (
        "product::declare_mul_self_abs",
        product::declare_mul_self_abs,
    ),
    (
        "order_extra::declare_order_extra_abs",
        order_extra::declare_order_extra_abs,
    ),
    (
        "lattice::declare_lattice_extra",
        lattice::declare_lattice_extra,
    ),
    (
        "uniform_convergence::declare_uniform_converges_on",
        uniform_convergence::declare_uniform_converges_on,
    ),
    (
        "archimedean_squeeze::declare_archimedean_squeeze",
        archimedean_squeeze::declare_archimedean_squeeze,
    ),
    (
        "archimedean::declare_archimedean",
        archimedean::declare_archimedean,
    ),
    ("density::declare_density", density::declare_density),
    (
        "cotransitivity::declare_cotransitivity",
        cotransitivity::declare_cotransitivity,
    ),
    (
        "completeness::declare_completeness",
        completeness::declare_completeness,
    ),
    (
        "convergence::declare_convergence",
        convergence::declare_convergence,
    ),
    (
        "uniform_continuity::declare_abs_add_le",
        uniform_continuity::declare_abs_add_le,
    ),
    (
        "uniform_continuity::declare_uniform_continuity",
        uniform_continuity::declare_uniform_continuity,
    ),
    (
        "uniform_continuity::declare_uniformly_continuous_on_restrict",
        uniform_continuity::declare_uniformly_continuous_on_restrict,
    ),
    ("crossing::declare_crossing", crossing::declare_crossing),
    (
        "convergence::declare_converges_comp_eventually",
        convergence::declare_converges_comp_eventually,
    ),
    (
        "derivative::declare_derivative",
        derivative::declare_derivative,
    ),
    (
        "deriv_unique::declare_deriv_unique",
        deriv_unique::declare_deriv_unique,
    ),
    ("fermat::declare_fermat", fermat::declare_fermat),
    ("rolle::declare_rolle", rolle::declare_rolle),
    ("mvt::declare_mvt", mvt::declare_mvt),
    (
        "uniform_continuity::declare_uniform_continuity_products",
        uniform_continuity::declare_uniform_continuity_products,
    ),
    (
        "uniform_continuity::declare_bucket_close",
        uniform_continuity::declare_bucket_close,
    ),
    (
        "uniform_continuity::declare_abs_bound_of_self",
        uniform_continuity::declare_abs_bound_of_self,
    ),
    (
        "uniform_continuity::declare_bounded_of_uniformly_continuous",
        uniform_continuity::declare_bounded_of_uniformly_continuous,
    ),
    (
        "mul_self_zero::declare_mul_self_zero",
        mul_self_zero::declare_mul_self_zero,
    ),
    (
        "crossing::declare_crossing_sample",
        crossing::declare_crossing_sample,
    ),
    (
        "crossing::declare_crossing_close",
        crossing::declare_crossing_close,
    ),
    (
        "crossing::declare_crossing_close_clamped",
        crossing::declare_crossing_close_clamped,
    ),
    (
        "crossing::declare_crossing_sample_pairing_close",
        crossing::declare_crossing_sample_pairing_close,
    ),
    ("sqrt::declare_sqrt", sqrt::declare_sqrt),
    ("speedup::declare_speedup", speedup::declare_speedup),
    (
        "sqrt::declare_sqrt_approx_kregular",
        sqrt::declare_sqrt_approx_kregular,
    ),
    ("sqrt::declare_sqrt_ctor", sqrt::declare_sqrt_ctor),
    ("sqrt::declare_sqrt_congr", sqrt::declare_sqrt_congr),
    ("sqrt::declare_sqrt_le_sqrt", sqrt::declare_sqrt_le_sqrt),
    ("sqrt::declare_sqrt_one", sqrt::declare_sqrt_one),
    ("sqrt::declare_sqrt_zero", sqrt::declare_sqrt_zero),
    ("sqrt::declare_sqrt_sq", sqrt::declare_sqrt_sq),
    ("sqrt::declare_sqrt_nonneg", sqrt::declare_sqrt_nonneg),
    ("sqrt::declare_mul_self_sqrt", sqrt::declare_mul_self_sqrt),
    ("sqrt::declare_sqrt_mul", sqrt::declare_sqrt_mul),
    ("sqrt::declare_le_of_sq_le", sqrt::declare_le_of_sq_le),
    (
        "convergence::declare_cauchy_convergence",
        convergence::declare_cauchy_convergence,
    ),
    ("series::declare_series", series::declare_series),
    (
        "uniform_continuity::declare_uniform_continuity_sums",
        uniform_continuity::declare_uniform_continuity_sums,
    ),
    ("monotone::declare_monotone", monotone::declare_monotone),
    ("integral::declare_integral", integral::declare_integral),
    (
        "integral::declare_sum_range_double",
        integral::declare_sum_range_double,
    ),
    (
        "integral::declare_sum_range_reblock",
        integral::declare_sum_range_reblock,
    ),
    (
        "integral::declare_within_of_two_sided_le",
        integral::declare_within_of_two_sided_le,
    ),
    (
        "integral::declare_le_add_of_abs_sub_le",
        integral::declare_le_add_of_abs_sub_le,
    ),
    (
        "integral::declare_two_sided_of_abs_sub_le",
        integral::declare_two_sided_of_abs_sub_le,
    ),
    (
        "uniform_convergence::declare_uniform_convergence_continuity",
        uniform_convergence::declare_uniform_convergence_continuity,
    ),
    (
        "uniform_convergence::declare_uniform_converges_add",
        uniform_convergence::declare_uniform_converges_add,
    ),
    (
        "uniform_convergence::declare_close_within_of_within",
        uniform_convergence::declare_close_within_of_within,
    ),
    (
        "integral::declare_close_within_of_within_indexed",
        integral::declare_close_within_of_within_indexed,
    ),
    (
        "uniform_convergence::declare_weierstrass_m_test",
        uniform_convergence::declare_weierstrass_m_test,
    ),
    ("integral::declare_of_nat_hom", integral::declare_of_nat_hom),
    (
        "monotone::declare_monotone_of_nonneg_deriv_all",
        monotone::declare_monotone_of_nonneg_deriv_all,
    ),
    (
        "derivative::declare_abs_diff_le_of_deriv_bound",
        derivative::declare_abs_diff_le_of_deriv_bound,
    ),
    (
        "derivative::declare_lipschitz_of_deriv_bound",
        derivative::declare_lipschitz_of_deriv_bound,
    ),
    (
        "derivative::declare_abs_diff_sub_le_of_deriv_bound",
        derivative::declare_abs_diff_sub_le_of_deriv_bound,
    ),
    (
        "uniform_convergence::declare_has_derivative_uniform_limit",
        uniform_convergence::declare_has_derivative_uniform_limit,
    ),
    (
        "integral::declare_fine_sample_in_bounds",
        integral::declare_fine_sample_in_bounds,
    ),
    (
        "integral::declare_fine_sample_close",
        integral::declare_fine_sample_close,
    ),
    (
        "integral::declare_fine_block_sum_close",
        integral::declare_fine_block_sum_close,
    ),
    (
        "integral::declare_mesh_reciprocal_mul",
        integral::declare_mesh_reciprocal_mul,
    ),
    (
        "integral::declare_equiv_abs_diff_le",
        integral::declare_equiv_abs_diff_le,
    ),
    (
        "integral::declare_sample_point_reblock",
        integral::declare_sample_point_reblock,
    ),
    (
        "integral::declare_reblock_block_eq_fine_block_sum",
        integral::declare_reblock_block_eq_fine_block_sum,
    ),
    (
        "integral::declare_riemann_sum_reblock_close",
        integral::declare_riemann_sum_reblock_close,
    ),
    (
        "integral::declare_riemann_sum_cauchy",
        integral::declare_riemann_sum_cauchy,
    ),
    (
        "integral::declare_shared_index_to_canonical",
        integral::declare_shared_index_to_canonical,
    ),
    (
        "integral::declare_riemann_sum_shared_accuracy_close",
        integral::declare_riemann_sum_shared_accuracy_close,
    ),
    // Generalizes the step above by exposing the shared mid-anchor `l`
    // as a genuine parameter; lands beside it for the same reason its
    // doc comment gives. Same requirement set: it is the same wiring.
    (
        "integral::declare_riemann_sum_shared_accuracy_close_at",
        integral::declare_riemann_sum_shared_accuracy_close_at,
    ),
    (
        "integral::declare_riemann_sum_total_eps_le",
        integral::declare_riemann_sum_total_eps_le,
    ),
    (
        "integral::declare_riemann_sum_deep_cauchy",
        integral::declare_riemann_sum_deep_cauchy,
    ),
    (
        "integral::declare_riemann_sum_deep_cauchy_folded",
        integral::declare_riemann_sum_deep_cauchy_folded,
    ),
    (
        "integral::declare_riemann_sum_deep_cauchy_cross",
        integral::declare_riemann_sum_deep_cauchy_cross,
    ),
    (
        "integral::declare_riemann_sum_deep_cauchy_cross_folded",
        integral::declare_riemann_sum_deep_cauchy_cross_folded,
    ),
    (
        "integral::declare_riemann_sum_add_cauchy_cross",
        integral::declare_riemann_sum_add_cauchy_cross,
    ),
    (
        "integral::declare_creal_integral",
        integral::declare_creal_integral,
    ),
    (
        "integral::declare_integral_converges",
        integral::declare_integral_converges,
    ),
    (
        "integral::declare_integral_const",
        integral::declare_integral_const,
    ),
    (
        "integral::declare_integral_witness_independent",
        integral::declare_integral_witness_independent,
    ),
    (
        "integral::declare_integral_add",
        integral::declare_integral_add,
    ),
    (
        "integral::declare_integral_le",
        integral::declare_integral_le,
    ),
    (
        "integral::declare_integral_scale",
        integral::declare_integral_scale,
    ),
    (
        "integral::declare_riemann_sum_integral_close",
        integral::declare_riemann_sum_integral_close,
    ),
    (
        "integral::declare_riemann_sum_split_exact",
        integral::declare_riemann_sum_split_exact,
    ),
    (
        "integral::declare_riemann_sum_split_scale_invariant",
        integral::declare_riemann_sum_split_scale_invariant,
    ),
    (
        "integral::declare_congr_of_uniformly_continuous",
        integral::declare_congr_of_uniformly_continuous,
    ),
    (
        "integral::declare_riemann_sum_split_exact_of_uc",
        integral::declare_riemann_sum_split_exact_of_uc,
    ),
    (
        "integral::declare_integral_split",
        integral::declare_integral_split,
    ),
    (
        "integral::declare_split_point_approx",
        integral::declare_split_point_approx,
    ),
    (
        "integral::declare_integral_endpoint_close",
        integral::declare_integral_endpoint_close,
    ),
    (
        "integral::declare_integral_split_arbitrary",
        integral::declare_integral_split_arbitrary,
    ),
    (
        "integral::declare_integral_abs_le",
        integral::declare_integral_abs_le,
    ),
    (
        "integral::declare_ftc_estimates",
        integral::declare_ftc_estimates,
    ),
    (
        "integral::declare_integral_eq_antideriv_diff",
        integral::declare_integral_eq_antideriv_diff,
    ),
    (
        "integral::declare_integral_by_parts",
        integral::declare_integral_by_parts,
    ),
    (
        "derivative::declare_has_derivative_integral_const",
        derivative::declare_has_derivative_integral_const,
    ),
    (
        "inverse_fn::declare_order_reflect_of_pos_deriv",
        inverse_fn::declare_order_reflect_of_pos_deriv,
    ),
    (
        "monotone::declare_inverse_lipschitz_of_pos_deriv",
        monotone::declare_inverse_lipschitz_of_pos_deriv,
    ),
    ("power::declare_power", power::declare_power),
    (
        "power::declare_power_series_term",
        power::declare_power_series_term,
    ),
    (
        "power::declare_power_series_term_congr",
        power::declare_power_series_term_congr,
    ),
    (
        "derivative::declare_has_derivative_pow_two",
        derivative::declare_has_derivative_pow_two,
    ),
    (
        "derivative::declare_has_derivative_pow",
        derivative::declare_has_derivative_pow,
    ),
    ("geometric::declare_geometric", geometric::declare_geometric),
    (
        "power::declare_power_series_term_abs_le",
        power::declare_power_series_term_abs_le,
    ),
    (
        "uniform_convergence::declare_power_series_uniform_converges",
        uniform_convergence::declare_power_series_uniform_converges,
    ),
    (
        "uniform_convergence::declare_converges_of_abs_diff_le",
        uniform_convergence::declare_converges_of_abs_diff_le,
    ),
    (
        "uniform_convergence::declare_uniform_converges_geom",
        uniform_convergence::declare_uniform_converges_geom,
    ),
    (
        "geometric::declare_geom_cauchy_of_lt_family",
        geometric::declare_geom_cauchy_of_lt_family,
    ),
    (
        "exponential::declare_exponential",
        exponential::declare_exponential,
    ),
    (
        "exponential::declare_geom_cauchy_family",
        exponential::declare_geom_cauchy_family,
    ),
    (
        "exponential::declare_exp_convergence",
        exponential::declare_exp_convergence,
    ),
    (
        "ratio_test::declare_geom_scaled_cauchy_of_lt",
        ratio_test::declare_geom_scaled_cauchy_of_lt,
    ),
    (
        "ratio_test::declare_sum_range_ratio_test",
        ratio_test::declare_sum_range_ratio_test,
    ),
    (
        "exponential::declare_e_family",
        exponential::declare_e_family,
    ),
    ("trig::declare_trig", trig::declare_trig),
    ("trig::declare_sin_trig", trig::declare_sin_trig),
    (
        "cos_sign::declare_converges_upper_bound_shift",
        cos_sign::declare_converges_upper_bound_shift,
    ),
    (
        "alternating::declare_alternating",
        alternating::declare_alternating,
    ),
    (
        "cos_sign::declare_alternating_upper_bound_tail",
        cos_sign::declare_alternating_upper_bound_tail,
    ),
    (
        "trig::declare_trig_alternating_bounds",
        trig::declare_trig_alternating_bounds,
    ),
    (
        "trig::declare_sin_trig_alternating_bounds",
        trig::declare_sin_trig_alternating_bounds,
    ),
    ("ivt::declare_ivt", ivt::declare_ivt),
    (
        "inverse_fn::declare_ivt_exact_root_at",
        inverse_fn::declare_ivt_exact_root_at,
    ),
    (
        "polynomial::declare_polynomial",
        polynomial::declare_polynomial,
    ),
    (
        "congruence::declare_congruence_extras",
        congruence::declare_congruence_extras,
    ),
    (
        "uniform_continuity::declare_bounded_on_id_zero_one",
        uniform_continuity::declare_bounded_on_id_zero_one,
    ),
    (
        "extreme_value::declare_extreme_value",
        extreme_value::declare_extreme_value,
    ),
    (
        "ivt_boundary::declare_ivt_boundary",
        ivt_boundary::declare_ivt_boundary,
    ),
    (
        "lub_boundary::declare_lub_boundary",
        lub_boundary::declare_lub_boundary,
    ),
    (
        "trig_fn::declare_cos_fn_family",
        trig_fn::declare_cos_fn_family,
    ),
    (
        "trig_fn::declare_cos_fn_equiv_cos_one",
        trig_fn::declare_cos_fn_equiv_cos_one,
    ),
    (
        "trig_fn::declare_cos_fn_wide_progress",
        trig_fn::declare_cos_fn_wide_progress,
    ),
    ("trig_fn::declare_cos_fn_wide", trig_fn::declare_cos_fn_wide),
    (
        "trig_fn::declare_cos_fn_wide_uniformly_continuous",
        trig_fn::declare_cos_fn_wide_uniformly_continuous,
    ),
    (
        "trig_fn::declare_cos_fn_wide_at_one",
        trig_fn::declare_cos_fn_wide_at_one,
    ),
    (
        "trig_fn::declare_has_derivative_on_restrict",
        trig_fn::declare_has_derivative_on_restrict,
    ),
    (
        "trig_fn::declare_sin_fn_term_family",
        trig_fn::declare_sin_fn_term_family,
    ),
    (
        "trig_fn::declare_sin_fn_dominant",
        trig_fn::declare_sin_fn_dominant,
    ),
    ("trig_fn::declare_sin_fn", trig_fn::declare_sin_fn),
    (
        "trig_fn::declare_sin_fn_uniformly_continuous",
        trig_fn::declare_sin_fn_uniformly_continuous,
    ),
    (
        "trig_fn::declare_cos_fn_derivative",
        trig_fn::declare_cos_fn_derivative,
    ),
    (
        "trig_fn::declare_cos_fn_wide_derivative",
        trig_fn::declare_cos_fn_wide_derivative,
    ),
    (
        "trig_fn::declare_sin_fn_lower_bound",
        trig_fn::declare_sin_fn_lower_bound,
    ),
    (
        "exp_fn::declare_exp_fn_family",
        exp_fn::declare_exp_fn_family,
    ),
    (
        "exp_fn::declare_exp_fn_equiv_e",
        exp_fn::declare_exp_fn_equiv_e,
    ),
    ("supremum::declare_max_range", supremum::declare_max_range),
    (
        "supremum::declare_max_range_transport",
        supremum::declare_max_range_transport,
    ),
    (
        "supremum::declare_mesh_level_count",
        supremum::declare_mesh_level_count,
    ),
    (
        "supremum::declare_mesh_level_count_pow",
        supremum::declare_mesh_level_count_pow,
    ),
    (
        "supremum::declare_mesh_level_count_ge_of_size",
        supremum::declare_mesh_level_count_ge_of_size,
    ),
    ("supremum::declare_mesh_max", supremum::declare_mesh_max),
    (
        "supremum::declare_mesh_max_step_le",
        supremum::declare_mesh_max_step_le,
    ),
    (
        "supremum::declare_mesh_max_mono",
        supremum::declare_mesh_max_mono,
    ),
    (
        "supremum::declare_exp_of_modulus",
        supremum::declare_exp_of_modulus,
    ),
    (
        "supremum::declare_true_exp_of_modulus",
        supremum::declare_true_exp_of_modulus,
    ),
    (
        "supremum::declare_true_exp_of_modulus_step_le",
        supremum::declare_true_exp_of_modulus_step_le,
    ),
    (
        "supremum::declare_true_exp_of_modulus_mono",
        supremum::declare_true_exp_of_modulus_mono,
    ),
    (
        "supremum::declare_exp_of_modulus_le_true_exp_of_modulus",
        supremum::declare_exp_of_modulus_le_true_exp_of_modulus,
    ),
    (
        "supremum::declare_mesh_point_near_coarse",
        supremum::declare_mesh_point_near_coarse,
    ),
    (
        "supremum::declare_max_range_le_add_of_exists",
        supremum::declare_max_range_le_add_of_exists,
    ),
    (
        "supremum::declare_mesh_max_le_add_of_step_close",
        supremum::declare_mesh_max_le_add_of_step_close,
    ),
    (
        "supremum::declare_mesh_max_le_add_of_modulus",
        supremum::declare_mesh_max_le_add_of_modulus,
    ),
    ("supremum::declare_sup_seq", supremum::declare_sup_seq),
    (
        "supremum::declare_sup_seq_cauchy",
        supremum::declare_sup_seq_cauchy,
    ),
    ("supremum::declare_sup_on", supremum::declare_sup_on),
    (
        "sup_laws::declare_max_range_attained_approx",
        sup_laws::declare_max_range_attained_approx,
    ),
    (
        "sup_laws::declare_sup_seq_le_shift",
        sup_laws::declare_sup_seq_le_shift,
    ),
    (
        "sup_laws::declare_sup_on_approx_lub",
        sup_laws::declare_sup_on_approx_lub,
    ),
    (
        "sup_laws::declare_sup_on_ub_at_sup_seq_point",
        sup_laws::declare_sup_on_ub_at_sup_seq_point,
    ),
    (
        "sup_laws::declare_step_family_locate",
        sup_laws::declare_step_family_locate,
    ),
    (
        "sup_laws::declare_sup_on_ub_at_fine_mesh_point",
        sup_laws::declare_sup_on_ub_at_fine_mesh_point,
    ),
    ("sup_laws::declare_sup_on_ub", sup_laws::declare_sup_on_ub),
    (
        "evt_row1::declare_evt_approx_max",
        evt_row1::declare_evt_approx_max,
    ),
    (
        "cos_sign::declare_cos_wide_tail_nonneg",
        cos_sign::declare_cos_wide_tail_nonneg,
    ),
    (
        "cos_sign::declare_cos_wide_tail_antitone",
        cos_sign::declare_cos_wide_tail_antitone,
    ),
    (
        "cos_sign::declare_cos_wide_series_converges",
        cos_sign::declare_cos_wide_series_converges,
    ),
    (
        "cos_sign::declare_cos_wide_nonpositive",
        cos_sign::declare_cos_wide_nonpositive,
    ),
    ("pi::declare_pi_family", pi::declare_pi_family),
];

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
    // `STEPS` is GENERATED from `STEP_DISPATCH` plus a measurement of this
    // module's source, so the two are the same list written twice and nothing
    // in the type system says so. A lane that adds a step to `STEP_DISPATCH`
    // and does not re-run `scripts/creal-declare-deps.py` would otherwise
    // build a prelude whose dependency graph silently omits it -- which is the
    // failure the generator exists to remove, arriving one level up. The
    // script's `--check` catches it too, but that is a gate somebody has to
    // run; this is the build itself, and 211 pointer comparisons cost nothing
    // against a prelude build measured in seconds.
    assert_eq!(
        STEPS.len(),
        STEP_DISPATCH.len(),
        "creal's generated STEPS table has {} entries against STEP_DISPATCH's \
         {} -- run `python3 scripts/creal-declare-deps.py` and commit \
         crates/axeyum-lean-kernel/src/creal/steps_generated.rs",
        STEPS.len(),
        STEP_DISPATCH.len(),
    );
    for (index, (step, &(label, run))) in STEPS.iter().zip(STEP_DISPATCH).enumerate() {
        assert!(
            step.label == label && std::ptr::fn_addr_eq(step.run, run),
            "creal's generated STEPS table disagrees with STEP_DISPATCH at \
             step {index}: '{}' vs '{label}'. Run `python3 \
             scripts/creal-declare-deps.py` and commit \
             crates/axeyum-lean-kernel/src/creal/steps_generated.rs",
            step.label,
        );
    }

    // The build order is COMPUTED from the dependency graph, not read off
    // `STEPS`'s array order -- §1's level-2 fix. Purely structural: no kernel
    // environment is involved, so this runs before any expensive work.
    //
    // Today's plan is `0..STEPS.len()`, byte-identically, because the array
    // order is already valid and the tie-break is the array index
    // (`plan_step_order`'s own docs, pinned by
    // `creal_tests::planned_order_is_the_array_order_today`). The difference
    // is what happens when it is NOT: a step moved earlier than its
    // dependency used to abort the build with a diagnosis, and is now simply
    // moved back. The phase-order class is unrepresentable rather than
    // reported.
    //
    // Measured, with the inversion `declare_projections` <-> `declare_carrier`
    // applied to the table below: the level-1 preflight refuses the build
    // (exit 101, "step 1 requires `CReal`, provider Some((2, ..))"), and this
    // planner produces a projection byte-identical to the unpermuted one --
    // same SHA-256 over all 14,673 rows.
    //
    // What the plan cannot see is a dependency the TABLE does not name, and
    // until 2026-09-01 that was most of them: the hand-written `STEPS` named
    // 3,934 of the 4,831 `requires` edges the code has, so 977 edges across
    // 175 of the 211 steps constrained nothing here. That is why the table is
    // now GENERATED from the source measurement rather than maintained
    // (`steps_generated`, written by `scripts/creal-declare-deps.py`): every
    // edge the analysis can see is in the table, so the planner constrains all
    // of them. What remains outside is what the analysis itself cannot see --
    // it is a static scan of `p.<field>` accessors through the call graph, so
    // a name reached other than through a `CRealPrelude` field is invisible to
    // it. See
    // `docs/research/11-design-review/2026-09-01-creal-declare-deps-measured.md`.
    let plan = match plan_step_order(prelude, STEPS) {
        Ok(plan) => plan,
        Err(PlanError::Duplicate(duplicate)) => panic!(
            "creal build order is unorderable: `{}` is claimed by BOTH step {} \
             ('{}') and step {} ('{}'), so 'the step that provides it' is not \
             a function. A step can only provide what it declares -- delete \
             the claim from whichever step does not.",
            render_name(kernel, duplicate.name),
            duplicate.first.0,
            duplicate.first.1,
            duplicate.second.0,
            duplicate.second.1,
        ),
        Err(PlanError::Order(violation)) => {
            let missing_text = render_name(kernel, violation.missing);
            let reason = match violation.provider {
                Some((provider_index, provider_label)) => format!(
                    "which step {provider_index} ('{provider_label}') \
                     declares, but that step cannot be scheduled first \
                     either -- the dependencies are CYCLIC, and no ordering \
                     satisfies them"
                ),
                None => "which no step in the build order declares -- the \
                          dependency table itself is incomplete, not just \
                          misordered"
                    .to_string(),
            };
            panic!(
                "creal prelude build order cannot be planned (see \
                 docs/research/11-design-review/\
                 2026-08-27-architecture-review.md \u{a7}1): step {} ('{}') \
                 requires `{missing_text}`, {reason}.",
                violation.consumer_index, violation.consumer_label,
            );
        }
    };
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<(), KernelError> {
        let mut d = IntDev::new(kernel, rat.int);
        // Runs `STEPS` in the PLANNED order rather than the array order.
        for &index in &plan {
            let step = &STEPS[index];
            // Name the step BEFORE propagating. A `KernelError` carries no
            // step identity, and the two errors this build produces most often
            // -- `UnboundFVar` and `TypeMismatch` -- name neither the
            // declaration nor the binder. A lane that has just added a
            // declaration will therefore attribute the failure to its own
            // work, which is the natural inference and was wrong:
            // `UnboundFVar { id: 17535 }` was blamed on `hclose_of_uc` for a
            // whole session when it came from `meshLevelCount_pow`, an
            // EARLIER step, whose `d.induct(..)` result was handed to
            // `add_declaration` without a `lam_fv` re-wrap. The lane's
            // free-variable tree-walk found nothing precisely because it
            // scanned the term it had written rather than the one that failed.
            //
            // `plan_step_order` immediately above already does this for
            // phase-order bugs; this is the same courtesy for proof failures.
            if let Err(error) = (step.run)(&mut d, prelude) {
                eprintln!(
                    "creal prelude build FAILED at step {index} ('{}') -- the \
                     error below belongs to THAT step, not to whichever \
                     declaration you last edited.",
                    step.label,
                );
                return Err(error);
            }
        }
        Ok(())
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

/// `Rat.natDivSucc k j`, with `k` a `Nat`-typed [`ExprId`] rather than a
/// literal — the rate-`K` companion of [`div_succ`], needed once the
/// accuracy family's numerator is a bound variable instead of a numeral. See
/// `creal/archimedean_squeeze.rs`.
fn div_succ_k(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, j])
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

mod alternating;
mod archimedean;
mod archimedean_squeeze;
mod cancellation;
mod completeness;
mod congruence;
mod convergence;
mod cos_sign;
mod cotransitivity;
mod crossing;
mod density;
mod deriv_unique;
mod derivative;
mod evt_row1;
mod exp_fn;
mod exponential;
mod extreme_value;
mod fermat;
mod field;
mod geometric;
mod integral;
mod inverse;
mod inverse_fn;
mod ivt;
mod ivt_boundary;
mod lattice;
mod lub_boundary;
mod monotone;
mod mul_self_zero;
mod mvt;
mod order_extra;
mod pi;
mod polynomial;
mod power;
mod product;
mod ratio_test;
mod ring_helpers;
mod rolle;
mod series;
mod speedup;
mod sqrt;
mod steps_generated;
mod sup_laws;
mod supremum;
mod trig;
mod trig_fn;
mod uniform_continuity;
mod uniform_convergence;

#[cfg(test)]
mod creal_tests;

/// Tests for `creal/lub_boundary.rs` (ADR-0603 row 2 for the least upper
/// bound property). Kept out of `creal_tests.rs` for the same reason the
/// inventory is sharded: that file is the append point every concurrent
/// `creal` lane collides on.
#[cfg(test)]
mod lub_boundary_tests;

/// Per-module declaration inventory consumed by `creal_tests`'s
/// environment-derived coverage test. `#[cfg(test)]`: pure test scaffolding,
/// not shipped in a release build. See `creal/inventory.rs` module docs for
/// why this exists (sharding the single 432-entry pinned array that used to
/// collide every pair of concurrent `creal` lanes).
#[cfg(test)]
mod inventory;

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
