//! **ℂ, constructed**: pairs of `CReal`s under a *defined* equality, costing
//! **zero** trusted declarations, and with the ordered-ring laws deliberately
//! absent — refuted, not merely omitted.
//!
//! This is ADR-0521
//! (`docs/research/09-decisions/adr-0521-complex-is-a-pair-setoid-over-creal-and-carries-no-order.md`),
//! and it continues ADR-0512 one layer up. `CReal` is a Bishop setoid of regular ℚ-sequences whose
//! equality is `CReal.Equiv`, a `Prop`-valued *definition* rather than `Eq`;
//! `Complex` inherits exactly that discipline:
//!
//! ```text
//! Complex.Equiv z w := CReal.Equiv (re z) (re w) ∧ CReal.Equiv (im z) (im w)
//! ```
//!
//! so `Eq Complex` is **not** the equality of complex numbers, every operation
//! owes a congruence lemma, and every law that mentions equality is stated over
//! `Complex.Equiv`. Nothing here needs `Quot.sound`, `funext` or `propext`, for
//! the same reason `CReal` did not: the quotient is never taken.
//!
//! # ℂ is a ring, and that is the *whole* of it
//!
//! `ArithPrelude`'s axiomatized `AxReal` package is an **ordered** commutative
//! ring: 22 laws, of which 13 mention `le` or `lt`. Nine do not, and those nine
//! — `add_comm`, `add_assoc`, `add_zero`, `add_neg`, `mul_comm`, `mul_assoc`,
//! `mul_one`, `mul_zero`, `left_distrib` — are exactly the ones proved here, in
//! `Complex.Equiv` form. See [`ComplexPrelude::ring_laws`].
//!
//! The other 13 are not *unavailable*; they are **jointly refutable**, and
//! [`ComplexPrelude::no_compatible_order`] says so as a theorem rather than as a
//! comment: for any two relations `le`, `lt` on `Complex` satisfying seven of
//! those 13 (reflexivity, irreflexivity of `lt`, `lt_of_le_of_lt`, `add_le_add`,
//! the setoid's `le_congr`, `sq_nonneg`, and `zero_lt_one`), `False` follows.
//! The witness is `I`: `sq_nonneg I` plus [`ComplexPrelude::i_sq`] gives
//! `0 ≤ −1`, adding `1` gives `1 ≤ 0`, and `0 < 1` closes it. **No** classical
//! reasoning is involved — the proof is a direct term, and `¬¬P → P` does not
//! exist in this logic prelude.
//!
//! That is the precise sense in which "ℂ is not ordered" is a *result* of this
//! module and not a scoping decision.
//!
//! # Why the component laws are cheap, and where the work actually went
//!
//! Every `Complex` law reduces, by `Complex.Equiv`'s definition, to two
//! `CReal.Equiv` obligations on the components — and those are *algebraic*
//! identities in a commutative ring, with no analysis left in them. The real
//! part of `(z·w)·v` and of `z·(w·v)` are the same four monomials in a different
//! order. Deriving each such rearrangement by hand from `add_comm`, `add_assoc`,
//! `mul_comm`, `mul_assoc`, `left_distrib` and the three congruences is where a
//! development of this shape goes wrong silently, so it is done once, by
//! decision procedure: [`ring`] normalizes a `CReal` expression to a sorted
//! multiset of signed monomials and emits the `Equiv` proof. It declares
//! nothing, so the `CReal` namespace is untouched and the trusted surface is
//! unchanged.
//!
//! # What is *not* claimed
//!
//! No order, by design and by [`ComplexPrelude::no_compatible_order`]. No
//! inverse, no division, no `√`, no completeness, no algebraic closure — each is
//! a separate development, and none of them is one of the nine. `Complex.normSq`
//! and [`ComplexPrelude::mul_conj`] land in `CReal`'s **existing** order
//! (`CReal.le`), which is available precisely because it is a statement about
//! the components rather than about ℂ.

// Proof scripts are long, straight-line term constructions with short
// mathematical names, exactly as in `creal` and `rat_prelude`.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    // The `declare_*` helpers take one-shot builder closures whose types are
    // read once, at the call site directly below them; naming them adds
    // indirection without adding meaning, and a `type` alias also fixes the
    // closure's captured lifetime, which these do not want.
    clippy::type_complexity
)]

use crate::BinderInfo;
use crate::CRealPrelude;
use crate::creal::build_creal_prelude;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::name::NameId;
use crate::nat_prelude::{NatOps, NatPrelude};
use crate::{Kernel, KernelError};

mod ring;

#[cfg(test)]
mod complex_tests;

use ring::{RExpr, cadd, cchain, ceq, cmul, cneg, cone, crefl, csymm, ctrans, czero, ring_proof};

/// Delta height for the leaf complex definitions: above every `CReal` one.
const LEAF_HEIGHT: u16 = 60;
/// Height for a definition that calls a leaf one.
const DERIVED_HEIGHT: u16 = 61;

/// The interned names produced by [`build_complex_prelude`].
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ComplexPrelude {
    /// The real development ℂ is constructed over. Its trusted surface is
    /// empty, which is what makes every law below empty too.
    pub creal: CRealPrelude,

    /// `Complex : Type` — a one-constructor inductive with two `CReal` fields.
    /// **Not** a quotient.
    pub complex: NameId,
    /// `Complex.mk : CReal → CReal → Complex`.
    pub mk: NameId,
    /// `Complex.rec` — the kernel-generated recursor.
    pub rec: NameId,
    /// `Complex.re : Complex → CReal`.
    pub re: NameId,
    /// `Complex.im : Complex → CReal`.
    pub im: NameId,

    /// `Complex.re_congr : ∀ z w, Equiv z w → CReal.Equiv (re z) (re w)`.
    pub re_congr: NameId,
    /// `Complex.im_congr : ∀ z w, Equiv z w → CReal.Equiv (im z) (im w)`.
    pub im_congr: NameId,

    /// `Complex.Equiv : Complex → Complex → Prop` — componentwise
    /// `CReal.Equiv`.
    ///
    /// **This, and not `Eq Complex`, is the equality of complex numbers.**
    pub equiv: NameId,
    /// `Complex.Equiv.refl`.
    pub equiv_refl: NameId,
    /// `Complex.Equiv.symm`.
    pub equiv_symm: NameId,
    /// `Complex.Equiv.trans`.
    pub equiv_trans: NameId,

    /// `Complex.ofReal : CReal → Complex` — the embedding ℝ ↪ ℂ, and the
    /// **non-vacuity** witness for the carrier.
    pub of_real: NameId,
    /// `Complex.I : Complex` — the imaginary unit, `ofReal 0 + i·1` written
    /// directly as the pair `(0, 1)`.
    pub i: NameId,
    /// `Complex.zero : Complex`.
    pub zero: NameId,
    /// `Complex.one : Complex`.
    pub one: NameId,

    /// `Complex.add : Complex → Complex → Complex`, componentwise.
    pub add: NameId,
    /// `Complex.neg : Complex → Complex`, componentwise.
    pub neg: NameId,
    /// `Complex.mul : Complex → Complex → Complex` — the **only** operation
    /// that mixes the components, and the reason ℂ is not just ℝ².
    pub mul: NameId,

    /// `Complex.add_congr` — the first setoid congruence obligation.
    pub add_congr: NameId,
    /// `Complex.neg_congr`.
    pub neg_congr: NameId,
    /// `Complex.mul_congr`.
    pub mul_congr: NameId,
    /// `Complex.conj_congr`.
    pub conj_congr: NameId,

    /// `Complex.add_comm` — one of the nine, in `Equiv` form.
    pub add_comm: NameId,
    /// `Complex.add_assoc` — one of the nine.
    pub add_assoc: NameId,
    /// `Complex.add_zero` — one of the nine.
    pub add_zero: NameId,
    /// `Complex.add_neg` — one of the nine.
    pub add_neg: NameId,
    /// `Complex.mul_comm` — one of the nine.
    pub mul_comm: NameId,
    /// `Complex.mul_assoc` — one of the nine, and the identity that pays for
    /// the ring calculus on its own: eight monomials, two orderings.
    pub mul_assoc: NameId,
    /// `Complex.mul_one` — one of the nine.
    pub mul_one: NameId,
    /// `Complex.mul_zero` — one of the nine.
    pub mul_zero: NameId,
    /// `Complex.left_distrib` — one of the nine.
    pub left_distrib: NameId,

    /// `Complex.ofReal_add : Equiv (add (ofReal a) (ofReal b)) (ofReal (a + b))`
    /// — the embedding is additive.
    pub of_real_add: NameId,
    /// `Complex.ofReal_mul : Equiv (mul (ofReal a) (ofReal b)) (ofReal (a · b))`.
    ///
    /// The **pinning** witness for the product: `mul_comm`, `mul_zero` and
    /// `left_distrib` all hold, footprint-free, of `fun _ _ => zero`. This
    /// fixes the operation on the whole embedded ℝ rather than asserting a
    /// property of it.
    pub of_real_mul: NameId,
    /// `Complex.I_sq : Equiv (mul I I) (neg one)`.
    ///
    /// The **pinning** witness for the imaginary unit — and the engine of
    /// [`Self::no_compatible_order`]. Without it `I` could be anything;
    /// `ofReal_mul` says nothing about it, because `I` is not in the image of
    /// `ofReal`.
    pub i_sq: NameId,
    /// `Complex.Equiv.not_zero_one : Not (Equiv zero one)` — the
    /// **discrimination** witness for the real component.
    pub not_zero_one: NameId,
    /// `Complex.Equiv.not_zero_I : Not (Equiv zero I)` — the discrimination
    /// witness for the *imaginary* component, and the statement that `I` is not
    /// `0`. An equivalence relation that relates everything is still an
    /// equivalence relation, and `not_zero_one` alone would not notice a
    /// `Complex.Equiv` that ignored the imaginary part entirely.
    pub not_zero_i: NameId,

    /// `Complex.re_add_im : ∀ z, Equiv z (add (ofReal (re z)) (mul I (ofReal
    /// (im z))))` — ℂ **is** ℝ², the reconstruction of `z` from its two real
    /// projections.
    pub re_add_im: NameId,

    /// `Complex.conj : Complex → Complex`.
    pub conj: NameId,
    /// `Complex.conj_conj : ∀ z, Equiv (conj (conj z)) z` — conjugation is an
    /// involution.
    pub conj_conj: NameId,
    /// `Complex.conj_add : ∀ z w, Equiv (conj (add z w)) (add (conj z) (conj w))`
    /// — conjugation is additive.
    pub conj_add: NameId,
    /// `Complex.conj_mul : ∀ z w, Equiv (conj (mul z w)) (mul (conj z) (conj w))`
    /// — conjugation is a ring homomorphism, the multiplicative half.
    pub conj_mul: NameId,
    /// `Complex.conj_sub : ∀ z w, Equiv (conj (add z (neg w)))
    /// (add (conj z) (neg (conj w)))` — conjugation is additive over
    /// subtraction too (`z − w := add z (neg w)`; no separate `Complex.sub` is
    /// declared, so the statement is over `add`/`neg` directly).
    pub conj_sub: NameId,
    /// `Complex.conj_ofReal : ∀ r, Equiv (conj (ofReal r)) (ofReal r)` — the
    /// embedded reals are conjugation-fixed.
    pub conj_of_real: NameId,
    /// `Complex.conj_I : Equiv (conj I) (neg I)`.
    pub conj_i: NameId,
    /// `Complex.eq_conj_iff_real : ∀ z, Iff (Equiv z (conj z))
    /// (CReal.Equiv (im z) CReal.zero)` — `z` is real exactly when it equals
    /// its own conjugate.
    ///
    /// Both directions are proved constructively. The forward direction needs
    /// `im z ~ CReal.zero` from `im z ~ CReal.neg (im z)`, i.e. that ℝ has no
    /// 2-torsion; that is proved here (not assumed) via `CReal.inv` at the
    /// constructed `two := CReal.add CReal.one CReal.one`, itself positive by
    /// `CReal.zero_lt_one` and `CReal.add_lt_add_of_le_of_lt` — no classical
    /// reasoning, no apartness convention beyond `CReal.PosBound`.
    pub eq_conj_iff_real: NameId,
    /// `Complex.normSq : Complex → CReal` — `re z ² + im z ²`, valued in ℝ
    /// because ℂ has no order to be nonneg *in*.
    pub norm_sq: NameId,
    /// `Complex.mul_conj : ∀ z, Equiv (mul z (conj z)) (ofReal (normSq z))`.
    ///
    /// The identity `z · z̄ = ‖z‖²`, and the one law whose imaginary part needs
    /// the ring calculus's **cancellation** pass: `a·(−b) + b·a` is two
    /// monomials that annihilate, not two that reorder.
    pub mul_conj: NameId,
    /// `Complex.normSq_nonneg : ∀ z, CReal.le CReal.zero (normSq z)` — the
    /// norm lands in `CReal`'s nonneg cone.
    pub norm_sq_nonneg: NameId,
    /// `Complex.normSq_conj : ∀ z, CReal.Equiv (normSq (conj z)) (normSq z)` —
    /// conjugation preserves the norm. Stated over `CReal.Equiv` directly:
    /// `normSq` is `CReal`-valued, so there is no `Complex.Equiv` to phrase it
    /// in.
    pub norm_sq_conj: NameId,
    /// `Complex.normSq_mul : ∀ z w, CReal.Equiv (normSq (mul z w))
    /// (CReal.mul (normSq z) (normSq w))` — the norm is multiplicative.
    ///
    /// The **Brahmagupta–Fibonacci two-square identity**,
    /// `(a²+b²)(c²+d²) = (ac−bd)² + (ad+bc)²`, decided by the same ring
    /// calculus as every law above: a degree-4 commutative-ring identity with
    /// no analysis in it, once expanded.
    pub norm_sq_mul: NameId,

    /// `Complex.normSq_pow : ∀ z (n : Nat), CReal.Equiv (normSq (pow z n))
    /// (CReal.pow (normSq z) n)` — the norm commutes with integer powers.
    ///
    /// Induction on `n`, mirroring [`Self::pow_add`]'s own shape: the base
    /// case reduces `normSq (pow z Nat.zero)` to `normSq Complex.one` by iota
    /// alone and closes the resulting `CReal` algebraic identity `one·one +
    /// zero·zero ~ one` with the ring calculus (the same move
    /// [`Self::i_is_fourth_root`] uses); the step chains [`Self::norm_sq_mul`]
    /// against the inductive hypothesis via `CReal.mul_congr`, landing
    /// exactly on `CReal.pow (normSq z) (Nat.succ j)`'s own iota-reduced
    /// shape (`CReal.mul (CReal.pow (normSq z) j) (normSq z)`) with no
    /// closing rearrangement needed.
    pub norm_sq_pow: NameId,

    /// `Complex.normSq_eq_zero_of_eq_zero : ∀ z, Equiv z zero →
    /// CReal.Equiv (normSq z) CReal.zero` — the **easy** half of
    /// `normSq z ~ 0 ↔ z ~ 0`.
    ///
    /// The converse is [`Self::eq_zero_of_norm_sq_eq_zero`], and the
    /// biconditional combining both is [`Self::norm_sq_eq_zero_iff`].
    pub norm_sq_eq_zero_of_eq_zero: NameId,
    /// `Complex.eq_zero_of_normSq_eq_zero : ∀ z, CReal.Equiv (normSq z)
    /// CReal.zero → Equiv z zero` — the **converse** half of
    /// `normSq z ~ 0 ↔ z ~ 0`.
    ///
    /// `normSq z` unfolds to `re z * re z + im z * im z`, a sum of two
    /// [`CRealPrelude::sq_nonneg`] terms; a zero sum of nonnegatives forces
    /// each addend to zero (an order argument built here from `add_zero`,
    /// `le_refl`, `add_le_add`, `le_congr`, `le_of_equiv`, `le_trans`,
    /// `equiv_of_le_le` and `add_comm` — no such split is a named `CReal`
    /// lemma), and then
    /// [`CRealPrelude::eq_zero_of_mul_self_zero`](crate::CRealPrelude::eq_zero_of_mul_self_zero)
    /// closes each component. That lemma is the genuine analytic estimate
    /// this development needed from `creal.rs`/`creal/`; everything above it
    /// is algebra plus the order laws.
    pub eq_zero_of_norm_sq_eq_zero: NameId,
    /// `Complex.normSq_eq_zero_iff : ∀ z, Iff (CReal.Equiv (normSq z)
    /// CReal.zero) (Equiv z zero)` — the full biconditional, from
    /// [`Self::norm_sq_eq_zero_of_eq_zero`] (`mpr`) and
    /// [`Self::eq_zero_of_norm_sq_eq_zero`] (`mp`). A restatement, not a new
    /// proof: the pattern `pythagoras_distSq` uses in `creal_point.rs`.
    pub norm_sq_eq_zero_iff: NameId,
    /// `Complex.normSq_add : ∀ z w, CReal.Equiv
    /// (add (normSq (add z w)) (normSq (add z (neg w))))
    /// (add (add (normSq z) (normSq z)) (add (normSq w) (normSq w)))` — the
    /// parallelogram law, `‖z+w‖² + ‖z−w‖² = 2‖z‖² + 2‖w‖²`, with `2·normSq z`
    /// written as `normSq z + normSq z` rather than a literal, to avoid
    /// inventing a convention for multiplying a `CReal` by a `Nat`. A clean
    /// unconditional identity, decided by the same ring calculus as
    /// [`Self::norm_sq_mul`].
    pub norm_sq_add: NameId,

    /// `Complex.no_compatible_order` — **ℂ admits no ordered-ring structure**,
    /// as a theorem. See the module documentation.
    pub no_compatible_order: NameId,

    /// `Complex.inv : (z : Complex) → (k : Nat) →
    /// CReal.PosBound (normSq z) k → Complex` —
    /// `inv z k h := mk (re z · CReal.inv (normSq z) k h)
    /// (−(im z · CReal.inv (normSq z) k h))`.
    ///
    /// Mirrors [`CReal.inv`](crate::CRealPrelude::inv)'s own signature
    /// exactly: the modulus `k` and the separating witness `h` are data the
    /// caller supplies, never derived from `z ≠ 0` — that disjunction cannot be
    /// eliminated into the `Type` this function returns. `normSq z` is the
    /// quantity the witness bounds away from zero, since ℂ itself carries no
    /// order to phrase positivity in.
    pub inv: NameId,
    /// `Complex.mul_inv_cancel : ∀ z k (h : CReal.PosBound (normSq z) k),
    /// Equiv (mul z (inv z k h)) one`.
    ///
    /// **The field law.** The real part reduces to
    /// `normSq z · CReal.inv (normSq z) k h`, which
    /// [`CReal.mul_inv_cancel`](crate::CRealPrelude::mul_inv_cancel) closes
    /// directly once the ring calculus rewrites the mixed product into that
    /// shape; the imaginary part cancels as a pure ring identity with no
    /// external fact needed at all.
    pub mul_inv_cancel: NameId,
    /// `Complex.inv_congr : ∀ z z' k k' (h : PosBound (normSq z) k)
    /// (h' : PosBound (normSq z') k'), Equiv z z' →
    /// Equiv (inv z k h) (inv z' k' h')`.
    ///
    /// Both moduli are quantified independently, exactly as
    /// [`CReal.inv_congr`](crate::CRealPrelude::inv_congr) is: two callers
    /// holding different separating witnesses for `Equiv`-related `z` and `z'`
    /// build different representative sequences underneath, and nothing forces
    /// `k = k'`. The proof needs `normSq z ~ normSq z'` first (a plain
    /// congruence in the components) and then leans on `CReal.inv_congr`
    /// itself — it is not a fresh estimate.
    pub inv_congr: NameId,

    /// `Complex.div z w k h := mul z (inv w k h)`, guarded by the DIVISOR's
    /// norm: `h : CReal.PosBound (normSq w) k`.
    pub div: NameId,
    /// `Complex.div_self : ∀ z k (h : PosBound (normSq z) k),
    /// Equiv (div z z k h) one` — `z / z ~ 1`, immediate from
    /// [`Self::mul_inv_cancel`] since `div z z k h` unfolds by one delta step
    /// to exactly `mul z (inv z k h)`.
    pub div_self: NameId,

    // --- apartness, and the constructive shape of "no zero divisors" --------
    //
    // ℂ has no order ([`Self::no_compatible_order`]), so `Complex.Apart`
    // cannot mirror `CReal.Apart`'s own *shape* (`lt x y ∨ lt y x`) — there is
    // no `lt` on `Complex` to disjoin. It mirrors `CReal.Apart`'s *role*
    // instead: a `Prop` strictly stronger than `Not Equiv`, built from a
    // strict positivity that already lives in the ordered `CReal` the
    // components are drawn from — [`Self::norm_sq`] of the difference.
    /// `Complex.Apart z w := CReal.lt CReal.zero (normSq (add z (neg w)))`.
    ///
    /// The one real quantity ℂ's missing order can still certify: `normSq` is
    /// always `CReal.le`-nonneg ([`Self::norm_sq_nonneg`]), so **strict**
    /// positivity of the difference's norm is exactly the separation
    /// `CReal.Apart` phrases via `lt` directly, ported across the one
    /// dimension where ℂ still has an order to borrow — `CReal`'s.
    pub apart: NameId,
    /// `Complex.apart_irrefl : ∀ z, Not (Apart z z)`.
    ///
    /// `add z (neg z)` has `normSq` computably `CReal.zero` (a pure
    /// commutative-ring identity, no analysis), so `Apart z z` would need
    /// `CReal.lt CReal.zero CReal.zero`, which `CReal.lt_irrefl` refuses.
    pub apart_irrefl: NameId,
    /// `Complex.apart_symm : ∀ z w, Apart z w → Apart w z`.
    ///
    /// `normSq (add w (neg z))` and `normSq (add z (neg w))` are the *same*
    /// degree-2 polynomial in the four real components — `(c−a)² = (a−c)²`
    /// monomial for monomial — so the ring calculus decides the bridging
    /// `CReal.Equiv` directly and `CReal.lt_congr` carries the hypothesis
    /// across it. No case split, no new estimate.
    pub apart_symm: NameId,
    /// `Complex.apart_of_normSq_pos : ∀ z, CReal.lt CReal.zero (normSq z) →
    /// Apart z Complex.zero`.
    ///
    /// The **linking** lemma between a positive norm and apartness from the
    /// origin — not definitionally free, because `Apart z zero` unfolds to
    /// positivity of `normSq (add z (neg zero))`, a *different* term from
    /// `normSq z` (though ring-equal to it: `add z (neg zero)` needs
    /// `add_zero`/pure rearrangement, not defeq). `CReal.lt_congr` carries the
    /// hypothesis across that ring identity.
    pub apart_of_normsq_pos: NameId,
    /// `Complex.mul_apart_zero : ∀ z w, Apart z zero → Apart w zero →
    /// Apart (mul z w) zero`.
    ///
    /// **The constructive shape of "ℂ has no zero divisors."** Both
    /// hypotheses give a positive norm (`Self::apart_of_normSq_pos`'s
    /// converse, inlined); `CReal.mul_pos` gives their product positive;
    /// [`Self::norm_sq_mul`] identifies that product with `normSq (mul z
    /// w)`; `Self::apart_of_normSq_pos`'s own bridging step closes it. See
    /// the module documentation for why the *disjunctive* form (`mul z w ~ 0
    /// → z ~ 0 ∨ w ~ 0`) is not attempted: `CReal`'s order is not decidable,
    /// so that disjunction is not known to be extractable, and this
    /// contrapositive-shaped statement is what *is* constructively available.
    pub mul_apart_zero: NameId,
    /// `Complex.mul_eq_zero_not_both_apart_zero : ∀ z w, Equiv (mul z w) zero
    /// → Not (And (Apart z zero) (Apart w zero))`.
    ///
    /// **The intuitionistically valid half of "no zero divisors."**
    /// `(A → ¬B) ↔ (B → ¬A)` holds without excluded middle (both are `A ∧ B →
    /// False`, curried), so this is [`Self::mul_apart_zero`] transposed
    /// against [`Self::norm_sq_eq_zero_of_eq_zero`] — no classical step
    /// anywhere. It is deliberately **not** stated as `¬(z ~ 0) ∧ ¬(w ~ 0) →
    /// ¬(mul z w ~ 0)`: that direction is the *contrapositive of the
    /// unavailable* disjunctive `mul_eq_zero`, and proving it here would
    /// silently recover what the module documentation says cannot be
    /// extracted. `Apart _ zero` is strictly stronger than `Not (Equiv _
    /// zero)`, and only the `Apart` form is proved.
    pub mul_eq_zero_not_both_apart_zero: NameId,

    // --- the other side of the field law, and complex powers ----------------
    /// `Complex.inv_mul_cancel : ∀ z k (h : CReal.PosBound (normSq z) k),
    /// Equiv (mul (inv z k h) z) one`.
    ///
    /// The other side of [`Self::mul_inv_cancel`], immediate from it and
    /// [`Self::mul_comm`] by one `Equiv.trans`: no fresh estimate, `inv` is
    /// not shown to be a *two-sided* inverse from scratch.
    pub inv_mul_cancel: NameId,
    /// `Complex.pos_bound_conj : ∀ z k, CReal.PosBound (normSq z) k →
    /// CReal.PosBound (normSq (conj z)) k`.
    ///
    /// **The modulus transports unchanged.** `CReal.PosBound x k` unfolds to
    /// `CReal.le (CReal.ofRat (Rat.natDivSucc 1 k)) x` — a lower bound that
    /// depends on `k` alone, not on `x` — so [`Self::norm_sq_conj`] (`normSq
    /// (conj z) ~ normSq z`) transports the same bound across the same `k` by
    /// `CReal.le_congr`, with no existential re-derivation through
    /// `CReal.pos_bound_of_lt` (which would hand back an unrelated modulus).
    /// This is what [`Self::conj_inv`] needs to state `inv (conj z)` at the
    /// caller's own `k`, and it is reusable at any other site that transports
    /// a `PosBound` witness across a `normSq`-`Equiv`.
    pub pos_bound_conj: NameId,
    /// `Complex.conj_inv : ∀ z k (h : CReal.PosBound (normSq z) k),
    /// Equiv (conj (inv z k h)) (inv (conj z) k (pos_bound_conj z k h))`.
    ///
    /// **Stated at the same `k`, via [`Self::pos_bound_conj`]** — not at some
    /// existentially-produced modulus for the conjugate, which would make the
    /// statement true but useless to a caller already holding `h` at `k`.
    /// `CReal.inv_congr` (independent-moduli form) relates
    /// `CReal.inv (normSq z) k h` and `CReal.inv (normSq (conj z)) k h'` via
    /// [`Self::norm_sq_conj`]; the rest is the ring calculus plus
    /// `CReal.mul_congr`/`neg_congr` on that one fact, componentwise.
    pub conj_inv: NameId,
    /// `Complex.pow : Complex → Nat → Complex`, by structural `Nat.rec` on the
    /// exponent — `pow z Nat.zero ≡ one`, `pow z (Nat.succ j) ≡ mul (pow z j)
    /// z` — matching `Int.pow`'s own convention exactly (`int_prelude/defs.rs`):
    /// recursion on the exponent, the recursive factor on the LEFT of the
    /// fresh copy of the base.
    pub pow: NameId,
    /// `Complex.pow_zero : ∀ z, Eq Complex (pow z Nat.zero) one`.
    ///
    /// Stated over `Eq Complex`, not `Complex.Equiv` — this is a fact about
    /// how `pow`'s *own* definition computes on one representative, the same
    /// reason `Int.pow_zero`/`Int.pow_succ` are `Eq Int` facts despite `Int`
    /// carrying its own equality discipline elsewhere. Closes by `Eq.refl`
    /// alone: `pow`'s `Nat.rec` application ι-reduces on `Nat.zero` with no
    /// further work.
    pub pow_zero: NameId,
    /// `Complex.pow_succ : ∀ z (m : Nat), Eq Complex (pow z (Nat.succ m))
    /// (mul (pow z m) z)`. Closes by `Eq.refl` alone, exactly as `pow_zero`
    /// does: `pow`'s `Nat.rec` application ι-reduces on `Nat.succ m` to
    /// precisely this right-hand side.
    pub pow_succ: NameId,
    /// `Complex.pow_add : ∀ z (m n : Nat), Equiv (pow z (Nat.add m n))
    /// (mul (pow z m) (pow z n))`.
    ///
    /// Induction on `n`, mirroring `Int.pow_add`'s own proof shape
    /// (`int_prelude/algebra.rs`) with every carrier promoted from `Int` to
    /// `Complex` and every step re-expressed over `Complex.Equiv`: the base
    /// case is [`Self::mul_one`] reversed, the step is the inductive
    /// hypothesis lifted by [`Self::mul_congr`] then [`Self::mul_assoc`].
    pub pow_add: NameId,

    // --- finite sums over ℂ, and the geometric series identity -------------
    /// `Complex.sumRange : (Nat → Complex) → Nat → Complex`, by structural
    /// `Nat.rec` on the bound — `sumRange f Nat.zero ≡ zero`, `sumRange f
    /// (Nat.succ j) ≡ add (sumRange f j) (f j)` — matching `Nat.sumRange`'s
    /// own convention exactly (`nat_prelude/defs.rs::declare_finite_ranges`):
    /// recursion on the bound, the new term added on the right of the prior
    /// sum. `sumRange f n` is `Σ_{k<n} f k`.
    pub sum_range: NameId,
    /// `Complex.sumRange_zero : ∀ f, Eq Complex (sumRange f Nat.zero) zero`.
    ///
    /// Closes by `Eq.refl` alone: `sumRange`'s `Nat.rec` application
    /// ι-reduces on `Nat.zero` with no further work, exactly
    /// [`Self::pow_zero`]'s own shape.
    pub sum_range_zero: NameId,
    /// `Complex.sumRange_succ : ∀ f (n : Nat), Eq Complex (sumRange f
    /// (Nat.succ n)) (add (sumRange f n) (f n))`. Closes by `Eq.refl` alone,
    /// exactly as [`Self::sum_range_zero`] does.
    pub sum_range_succ: NameId,
    /// `Complex.sumRange_congr : ∀ f g n, (∀ i, Equiv (f i) (g i)) → Equiv
    /// (sumRange f n) (sumRange g n)`.
    ///
    /// Induction on `n` — `Complex.Equiv` is a *defined* relation, not `Eq`,
    /// so nothing rewrites under the sum for free, and this proof is the only
    /// route to moving a pointwise fact under a `Complex.sumRange`. Mirrors
    /// `Nat.sumRange_congr`'s own proof shape (`nat_prelude/algebra.rs`) with
    /// every step promoted from `Eq Nat` to `Complex.Equiv`.
    pub sum_range_congr: NameId,
    /// `Complex.mul_sumRange : ∀ w f n, Equiv (mul w (sumRange f n))
    /// (sumRange (fun i => mul w (f i)) n)` — a constant distributes through
    /// a finite sum. Induction on `n` plus [`Self::left_distrib`], mirroring
    /// `Nat.mul_sumRange`'s own proof shape.
    pub mul_sum_range: NameId,
    /// `Complex.mul_sub_one_geom : ∀ z (n : Nat), Equiv (mul (add one (neg z))
    /// (sumRange (fun k => pow z k) n)) (add one (neg (pow z n)))` — **the
    /// geometric series identity**, `(1 − z) · Σ_{k<n} z^k = 1 − z^n`, holding
    /// for every `z : Complex` including `z ~ 1` (where the corresponding
    /// quotient identity is meaningless).
    ///
    /// Stated multiplied through rather than as a quotient: the quotient form
    /// needs `inv (add one (neg z)) k h` for a witnessed `CReal.PosBound
    /// (normSq (add one (neg z))) k`, which is not available for an
    /// arbitrary `z` — reaching it from `z ≁ 1` alone would be Markov's
    /// principle, which this kernel neither proves nor assumes. Induction on
    /// `n`, telescoping: the base case erases the sum via `mul_zero` and
    /// `add_neg`; the step distributes over the freshly extended sum with
    /// `left_distrib`, substitutes the inductive hypothesis via
    /// [`Self::add_congr`], then closes the remaining two-term identity
    /// `(1 − zⁿ) + (1 − z)·zⁿ = 1 − zⁿ·z` — a pure ring identity once the
    /// hypothesis is in place — by the `ring` calculus over the atoms `z` and
    /// `zⁿ`.
    pub mul_sub_one_geom: NameId,
    /// `Complex.geom_series_div : ∀ z (n k : Nat) (h : CReal.PosBound (normSq
    /// (add one (neg z))) k), Equiv (sumRange (fun j => pow z j) n) (div (add
    /// one (neg (pow z n))) (add one (neg z)) k h)`.
    ///
    /// The quotient corollary of [`Self::mul_sub_one_geom`], stated
    /// **honestly**: the modulus witness `k`/`h` for `1 − z` is an explicit
    /// argument, exactly as [`Self::inv`] and [`Self::conj_inv`] take theirs
    /// — never derived from `z ≁ 1` alone, which this kernel cannot do without
    /// Markov's principle. Cancels `(1 − z)` against its own inverse via
    /// [`Self::inv_mul_cancel`], [`Self::mul_assoc`] and [`Self::mul_comm`],
    /// with no fresh analysis beyond [`Self::mul_sub_one_geom`] itself.
    pub geom_series_div: NameId,

    // --- the ℕ → ℂ cast --------------------------------------------------
    /// `Complex.ofNat : Nat → Complex`, by structural `Nat.rec` on the
    /// argument — `ofNat Nat.zero ≡ zero`, `ofNat (Nat.succ j) ≡ add (ofNat j)
    /// one` — matching [`Self::pow`]/[`Self::sum_range`]'s own convention:
    /// recursion via `Nat.rec` directly, not via the three-deep
    /// `ofReal ∘ CReal.ofRat ∘ Rat.ofInt ∘ Int.ofNat` chain already available.
    /// A direct definition needs no lemma about how those three casts compose,
    /// and makes [`Self::of_nat_add`]/[`Self::of_nat_mul`] themselves plain
    /// inductions rather than transports across three intermediate carriers.
    ///
    /// **Known gap**: this `ofNat` is not shown (and is not claimed) to agree,
    /// even propositionally, with `ofReal ∘ CReal.ofRat ∘ Rat.ofInt ∘
    /// Int.ofNat` — a caller needing both casts to coincide needs its own
    /// bridging lemma, not proved here.
    pub of_nat: NameId,
    /// `Complex.ofNat_zero : Eq Complex (ofNat Nat.zero) zero`. Closes by
    /// `Eq.refl` alone, exactly [`Self::pow_zero`]'s own shape.
    pub of_nat_zero: NameId,
    /// `Complex.ofNat_succ : ∀ n, Eq Complex (ofNat (Nat.succ n)) (add (ofNat
    /// n) one)`. Closes by `Eq.refl` alone, exactly [`Self::pow_succ`]'s own
    /// shape.
    pub of_nat_succ: NameId,
    /// `Complex.ofNat_add : ∀ m n, Equiv (ofNat (Nat.add m n)) (add (ofNat m)
    /// (ofNat n))` — `ofNat` is an additive homomorphism.
    ///
    /// Induction on `n`, mirroring [`Self::pow_add`]'s own proof shape with
    /// `add`/`add_assoc`/`add_congr` in place of `mul`/`mul_assoc`/
    /// `mul_congr`, and the base case [`Self::add_zero`] reversed in place of
    /// [`Self::mul_one`] reversed.
    pub of_nat_add: NameId,
    /// `Complex.ofNat_mul : ∀ m n, Equiv (ofNat (Nat.mul m n)) (mul (ofNat m)
    /// (ofNat n))` — `ofNat` is a multiplicative homomorphism.
    ///
    /// Induction on `n`: the base case is [`Self::mul_zero`] reversed; the
    /// step unfolds `Nat.mul m (Nat.succ j)` to `Nat.add (Nat.mul m j) m`,
    /// applies [`Self::of_nat_add`] to cast that ℕ-sum, substitutes the
    /// inductive hypothesis via [`Self::add_congr`], then matches the
    /// `ofNat (Nat.succ j)`-unfolded right-hand side via
    /// [`Self::left_distrib`] and [`Self::mul_one`].
    pub of_nat_mul: NameId,

    // --- finite sums' additive homomorphism, and a bounded reindex ---------
    /// `Complex.sumRange_add : ∀ f g n, Equiv (sumRange (fun i => add (f i) (g
    /// i)) n) (add (sumRange f n) (sumRange g n))`.
    ///
    /// Induction on `n`, mirroring `Nat.sumRange_add`'s own proof shape
    /// (`nat_prelude/binomial.rs::declare_sum_range_add`): the successor case
    /// needs the four-term rearrangement `(A+B)+(C+D) ~ (A+C)+(B+D)`, closed
    /// here by `ring_law_proof` over the four summands as opaque atoms
    /// rather than by a hand-built `add_left_comm`/`add_add_add_comm` — the
    /// decision procedure the ℕ proof did not have available.
    pub sum_range_add: NameId,
    /// `Complex.sumRange_shiftFront : ∀ f n, Equiv (sumRange f (Nat.succ n))
    /// (add (f Nat.zero) (sumRange (fun k => f (Nat.succ k)) n))` — peeling
    /// the FRONT term off a finite sum ([`Self::sum_range_succ`] already peels
    /// the back term for free).
    ///
    /// Induction on `n`, mirroring `Nat.sumRange_shiftFront`'s own proof shape
    /// (`nat_prelude/binomial.rs::declare_sum_range_shift_front`); the
    /// successor step's reassociation closes by `ring_law_proof`.
    pub sum_range_shift_front: NameId,
    /// `Complex.sumRange_congr_lt : ∀ f g n, (∀ i, Nat.lt i n → Equiv (f i) (g
    /// i)) → Equiv (sumRange f n) (sumRange g n)` — [`Self::sum_range_congr`]
    /// with the hypothesis weakened to indices below the bound, which is what
    /// a sum with only-conditionally-true summand identities (e.g. involving
    /// truncated `Nat` subtraction) can actually supply.
    ///
    /// Induction on `n`, mirroring `Nat.sumRange_congr_lt`'s own proof shape
    /// (`nat_prelude/binomial.rs::declare_sum_range_congr_lt`).
    pub sum_range_congr_lt: NameId,
    /// `Complex.sumRange_split : ∀ f m n, Equiv (sumRange f (Nat.add m n))
    /// (add (sumRange f m) (sumRange (fun k => f (Nat.add m k)) n))`.
    ///
    /// ℝ already has this ([`CRealPrelude::sum_range_split`]); ℂ did not.
    /// Induction on `n`, mirroring `CReal.sumRange_split`'s own proof shape
    /// (`creal/series.rs::declare_sum_range_split`) verbatim with every step
    /// promoted from `CReal.Equiv` to `Complex.Equiv`: both cases close
    /// purely by `Nat.add`'s own iota-reduction (`add m Nat.zero ≡ m`, `add m
    /// (Nat.succ j) ≡ Nat.succ (add m j)`) plus one
    /// [`Self::add_zero`]/[`Self::add_assoc`] respectively — no ring calculus
    /// needed, the same reason the `CReal` original needs none. This is what
    /// turns any statement about a series tail into one about partial sums.
    pub sum_range_split: NameId,

    // --- the binomial theorem -----------------------------------------------
    /// `Complex.add_pow : ∀ a b n, Equiv (pow (add a b) n) (sumRange (fun k =>
    /// mul (mul (ofNat (Nat.choose n k)) (pow a k)) (pow b (Nat.sub n k)))
    /// (Nat.succ n))` — **the binomial theorem over ℂ**.
    ///
    /// The exponent, the summation bound, `Nat.choose` and `Nat.sub` are all
    /// `Nat`-valued throughout, exactly as `Nat.add_pow`'s own statement is;
    /// only the coefficient `Nat.choose n k` is cast into `Complex` via
    /// [`Self::of_nat`], and `a`, `b` range over `Complex`. Sum runs to
    /// `Nat.succ n` because [`Self::sum_range`] is exclusive
    /// (`sumRange f n = Σ_{k<n} f k`), matching `Nat.add_pow`'s own index
    /// convention. Induction on `n`, mirroring `Nat.add_pow`'s own proof shape
    /// (`nat_prelude/binomial.rs::declare_add_pow`) with every ring step over
    /// `Complex.Equiv` closed by `ring_law_proof` wherever it is a pure
    /// algebraic rearrangement, and the `Nat`-side Pascal/`sub` reasoning
    /// (`choose_succ_succ`, `succ_sub_succ`, `choose_succ_self_eq_zero`,
    /// `choose_zero_right`) lifted into a `Complex` context via
    /// `nat_eq_to_complex_equiv`.
    pub add_pow: NameId,

    // --- roots of unity and the finite Fourier orthogonality relation -------
    /// `Complex.IsRootOfUnity : Complex → Nat → Prop := fun z n => Equiv (pow
    /// z n) one`.
    ///
    /// A `Definition`, not a fresh predicate with its own laws: every fact
    /// below unfolds it by one delta step to `pow z n ~ one` and works with
    /// that directly, exactly [`Self::apart`]'s own convention.
    pub is_root_of_unity: NameId,
    /// `Complex.one_is_root_of_unity : ∀ n, IsRootOfUnity one n` — the
    /// **non-vacuity** witness shared by every `n`.
    pub one_is_root_of_unity: NameId,
    /// `Complex.I_is_fourth_root : IsRootOfUnity I 4`.
    ///
    /// The **negative control**: a predicate satisfied only by `one` would be
    /// nearly vacuous, and `I` is the cheapest genuinely different witness.
    /// Closed by unfolding `pow I 4` down to `mul (mul (mul (mul one I) I) I)
    /// I` by iota alone (definitionally what four applications of
    /// [`Self::pow_succ`] plus one of [`Self::pow_zero`] assert) and then
    /// deciding that fully-expanded product with the ring calculus, which
    /// already carries `I`'s components `(0, 1)` — the same fact
    /// [`Self::i_sq`] states — so no separate appeal to `i_sq` is needed
    /// beyond what the calculus already knows about `I`.
    pub i_is_fourth_root: NameId,
    /// `Complex.pow_mul : ∀ z (m n : Nat), Equiv (pow z (Nat.mul m n)) (pow
    /// (pow z m) n)`.
    ///
    /// Induction on `n`, mirroring `Int.pow_mul`'s own proof shape
    /// (`int_prelude/algebra.rs::declare_pow_mul`) with every step promoted
    /// from `Eq Int` to `Complex.Equiv`: the base case computes both sides to
    /// `one` (`Nat.mul m Nat.zero` and `pow _ Nat.zero` both ι-reduce), the
    /// step chains [`Self::pow_add`] then the inductive hypothesis, and the
    /// result of that chain is *already* `pow (pow z m) (Nat.succ j)` up to
    /// ι-reduction — no closing rearrangement needed, unlike `pow_add`
    /// itself.
    pub pow_mul: NameId,
    /// `Complex.geom_sum_eq_zero_of_root_of_unity : ∀ z n, IsRootOfUnity z n
    /// → Apart (add one (neg z)) zero → Equiv (sumRange (fun k => pow z k)
    /// n) zero`.
    ///
    /// **The finite Fourier orthogonality relation, `Σ_{k<n} zᵏ = 0` for `z`
    /// an `n`-th root of unity with `z ≠ 1`.**
    ///
    /// The classical hypothesis is `z ≠ 1`; `¬(z ~ one)` **cannot** reach
    /// `Apart (add one (neg z)) zero` in this kernel — that converse is
    /// Markov's principle, proved nowhere here — so the hypothesis is stated
    /// as the positive `Apart (add one (neg z)) zero` directly, exactly
    /// [`Self::geom_series_div`]'s own convention for the same quantity.
    ///
    /// Proof: [`Self::mul_sub_one_geom`] gives `Equiv (mul (add one (neg z))
    /// S) (add one (neg (pow z n)))`, and the hypothesis `pow z n ~ one`
    /// rewrites the right side to `zero` (via [`Self::neg_congr`],
    /// [`Self::add_congr`], [`Self::add_neg`]), so `mul (add one (neg z)) S ~
    /// zero`. The `Apart` hypothesis is unfolded (the same `normSq`-shift
    /// used by [`Self::mul_apart_zero`]) into `CReal.lt CReal.zero (normSq
    /// (add one (neg z)))`, and `CReal.pos_bound_of_lt` extracts a modulus
    /// `k`/witness `h` existentially (via `exists_elim`, never via `¬¬P →
    /// P`); `Complex.inv (add one (neg z)) k h` then cancels against the
    /// product exactly as [`Self::geom_series_div`] cancels its own divisor.
    pub geom_sum_eq_zero_of_root_of_unity: NameId,
    /// `Complex.root_of_unity_mul : ∀ z w n, IsRootOfUnity z n →
    /// IsRootOfUnity w n → IsRootOfUnity (mul z w) n` — the `n`-th roots of
    /// unity are closed under multiplication.
    ///
    /// Needs `(z·w)ⁿ ~ zⁿ·wⁿ`, which is not one of the declared lemmas above;
    /// proved inline by induction on `n` (the step is a four-atom
    /// commutative rearrangement `(A·B)·(z·w) ~ (A·z)·(B·w)` decided by the
    /// ring calculus over the opaque atoms `A := zʲ`, `B := wʲ`, `z`, `w`),
    /// then `mul_congr` substitutes both hypotheses and [`Self::mul_one`]
    /// (at `one`) closes `mul one one ~ one`.
    pub root_of_unity_mul: NameId,
    /// `Complex.root_of_unity_pow : ∀ z m n, IsRootOfUnity z n →
    /// IsRootOfUnity (pow z m) n` — the `n`-th roots of unity are closed
    /// under taking powers.
    ///
    /// `(zᵐ)ⁿ ~ z^(m·n) ~ z^(n·m) ~ (zⁿ)ᵐ ~ oneᵐ ~ one`: two uses of
    /// [`Self::pow_mul`], `Nat.mul_comm` lifted by `nat_eq_to_complex_equiv`,
    /// a congruence of `pow` in its *base* argument (proved inline by
    /// induction on the exponent — not one of the declared lemmas above
    /// either), and [`Self::one_is_root_of_unity`].
    ///
    /// Together with [`Self::root_of_unity_mul`] and
    /// [`Self::one_is_root_of_unity`] this is every group axiom the `n`-th
    /// roots of unity satisfy that is **statable** here: closure and an
    /// identity. **Inverses are not** — `Complex.inv` needs a witnessed
    /// `CReal.PosBound (normSq z) k`, which `IsRootOfUnity z n` does not
    /// supply (a root of unity is automatically apart from zero, since
    /// `normSq z` th power is `one`'s norm, but extracting the modulus and
    /// showing `inv z k h` is again an `n`-th root of unity is a separate
    /// development, not attempted here).
    pub root_of_unity_pow: NameId,
}

impl ComplexPrelude {
    /// The nine commutative-**ring** laws over `Complex`, in the declaration
    /// order of the `AxReal` package.
    ///
    /// These are exactly the `AxReal` package's 22 ordered-commutative-ring laws
    /// **minus** the 13 that mention `le` or `lt`. The omission is not a gap:
    /// [`Self::no_compatible_order`] proves that no `le`/`lt` on `Complex` can
    /// satisfy them. All nine mention equality in the axiomatized package and
    /// are therefore stated here over [`Complex.Equiv`](Self::equiv), because
    /// `Eq Complex` is not the equality of complex numbers.
    ///
    /// This list exists so that "9 of 9" is read out of the kernel by a test
    /// rather than asserted in prose.
    #[must_use]
    pub fn ring_laws(&self) -> [NameId; 9] {
        [
            self.add_comm,
            self.add_assoc,
            self.add_zero,
            self.add_neg,
            self.mul_comm,
            self.mul_assoc,
            self.mul_one,
            self.mul_zero,
            self.left_distrib,
        ]
    }
}

fn intern_names(kernel: &mut Kernel, creal: CRealPrelude) -> ComplexPrelude {
    let anon = kernel.anon();
    let complex = kernel.name_str(anon, "Complex");
    let equiv = kernel.name_str(complex, "Equiv");
    ComplexPrelude {
        creal,
        complex,
        mk: kernel.name_str(complex, "mk"),
        rec: kernel.name_str(complex, "rec"),
        re: kernel.name_str(complex, "re"),
        im: kernel.name_str(complex, "im"),
        re_congr: kernel.name_str(complex, "re_congr"),
        im_congr: kernel.name_str(complex, "im_congr"),
        equiv,
        equiv_refl: kernel.name_str(equiv, "refl"),
        equiv_symm: kernel.name_str(equiv, "symm"),
        equiv_trans: kernel.name_str(equiv, "trans"),
        of_real: kernel.name_str(complex, "ofReal"),
        i: kernel.name_str(complex, "I"),
        zero: kernel.name_str(complex, "zero"),
        one: kernel.name_str(complex, "one"),
        add: kernel.name_str(complex, "add"),
        neg: kernel.name_str(complex, "neg"),
        mul: kernel.name_str(complex, "mul"),
        add_congr: kernel.name_str(complex, "add_congr"),
        neg_congr: kernel.name_str(complex, "neg_congr"),
        mul_congr: kernel.name_str(complex, "mul_congr"),
        conj_congr: kernel.name_str(complex, "conj_congr"),
        add_comm: kernel.name_str(complex, "add_comm"),
        add_assoc: kernel.name_str(complex, "add_assoc"),
        add_zero: kernel.name_str(complex, "add_zero"),
        add_neg: kernel.name_str(complex, "add_neg"),
        mul_comm: kernel.name_str(complex, "mul_comm"),
        mul_assoc: kernel.name_str(complex, "mul_assoc"),
        mul_one: kernel.name_str(complex, "mul_one"),
        mul_zero: kernel.name_str(complex, "mul_zero"),
        left_distrib: kernel.name_str(complex, "left_distrib"),
        of_real_add: kernel.name_str(complex, "ofReal_add"),
        of_real_mul: kernel.name_str(complex, "ofReal_mul"),
        i_sq: kernel.name_str(complex, "I_sq"),
        not_zero_one: kernel.name_str(equiv, "not_zero_one"),
        not_zero_i: kernel.name_str(equiv, "not_zero_I"),
        re_add_im: kernel.name_str(complex, "re_add_im"),
        conj: kernel.name_str(complex, "conj"),
        conj_conj: kernel.name_str(complex, "conj_conj"),
        conj_add: kernel.name_str(complex, "conj_add"),
        conj_mul: kernel.name_str(complex, "conj_mul"),
        conj_sub: kernel.name_str(complex, "conj_sub"),
        conj_of_real: kernel.name_str(complex, "conj_ofReal"),
        conj_i: kernel.name_str(complex, "conj_I"),
        eq_conj_iff_real: kernel.name_str(complex, "eq_conj_iff_real"),
        norm_sq: kernel.name_str(complex, "normSq"),
        mul_conj: kernel.name_str(complex, "mul_conj"),
        norm_sq_nonneg: kernel.name_str(complex, "normSq_nonneg"),
        norm_sq_conj: kernel.name_str(complex, "normSq_conj"),
        norm_sq_mul: kernel.name_str(complex, "normSq_mul"),
        norm_sq_pow: kernel.name_str(complex, "normSq_pow"),
        norm_sq_eq_zero_of_eq_zero: kernel.name_str(complex, "normSq_eq_zero_of_eq_zero"),
        eq_zero_of_norm_sq_eq_zero: kernel.name_str(complex, "eq_zero_of_normSq_eq_zero"),
        norm_sq_eq_zero_iff: kernel.name_str(complex, "normSq_eq_zero_iff"),
        norm_sq_add: kernel.name_str(complex, "normSq_add"),
        no_compatible_order: kernel.name_str(complex, "no_compatible_order"),
        inv: kernel.name_str(complex, "inv"),
        mul_inv_cancel: kernel.name_str(complex, "mul_inv_cancel"),
        inv_congr: kernel.name_str(complex, "inv_congr"),
        div: kernel.name_str(complex, "div"),
        div_self: kernel.name_str(complex, "div_self"),
        apart: kernel.name_str(complex, "Apart"),
        apart_irrefl: kernel.name_str(complex, "apart_irrefl"),
        apart_symm: kernel.name_str(complex, "apart_symm"),
        apart_of_normsq_pos: kernel.name_str(complex, "apart_of_normSq_pos"),
        mul_apart_zero: kernel.name_str(complex, "mul_apart_zero"),
        mul_eq_zero_not_both_apart_zero: kernel
            .name_str(complex, "mul_eq_zero_not_both_apart_zero"),
        inv_mul_cancel: kernel.name_str(complex, "inv_mul_cancel"),
        pos_bound_conj: kernel.name_str(complex, "pos_bound_conj"),
        conj_inv: kernel.name_str(complex, "conj_inv"),
        pow: kernel.name_str(complex, "pow"),
        pow_zero: kernel.name_str(complex, "pow_zero"),
        pow_succ: kernel.name_str(complex, "pow_succ"),
        pow_add: kernel.name_str(complex, "pow_add"),
        sum_range: kernel.name_str(complex, "sumRange"),
        sum_range_zero: kernel.name_str(complex, "sumRange_zero"),
        sum_range_succ: kernel.name_str(complex, "sumRange_succ"),
        sum_range_congr: kernel.name_str(complex, "sumRange_congr"),
        mul_sum_range: kernel.name_str(complex, "mul_sumRange"),
        mul_sub_one_geom: kernel.name_str(complex, "mul_sub_one_geom"),
        geom_series_div: kernel.name_str(complex, "geom_series_div"),
        of_nat: kernel.name_str(complex, "ofNat"),
        of_nat_zero: kernel.name_str(complex, "ofNat_zero"),
        of_nat_succ: kernel.name_str(complex, "ofNat_succ"),
        of_nat_add: kernel.name_str(complex, "ofNat_add"),
        of_nat_mul: kernel.name_str(complex, "ofNat_mul"),
        sum_range_add: kernel.name_str(complex, "sumRange_add"),
        sum_range_shift_front: kernel.name_str(complex, "sumRange_shiftFront"),
        sum_range_congr_lt: kernel.name_str(complex, "sumRange_congr_lt"),
        sum_range_split: kernel.name_str(complex, "sumRange_split"),
        add_pow: kernel.name_str(complex, "add_pow"),
        is_root_of_unity: kernel.name_str(complex, "IsRootOfUnity"),
        one_is_root_of_unity: kernel.name_str(complex, "one_is_root_of_unity"),
        i_is_fourth_root: kernel.name_str(complex, "I_is_fourth_root"),
        pow_mul: kernel.name_str(complex, "pow_mul"),
        geom_sum_eq_zero_of_root_of_unity: kernel
            .name_str(complex, "geom_sum_eq_zero_of_root_of_unity"),
        root_of_unity_mul: kernel.name_str(complex, "root_of_unity_mul"),
        root_of_unity_pow: kernel.name_str(complex, "root_of_unity_pow"),
    }
}

/// Build the complex prelude: ℂ as pairs of constructed reals, **asserting
/// nothing**.
///
/// Idempotent on a kernel that already carries it. A failure rolls the
/// environment back to the pre-call state.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub fn build_complex_prelude(kernel: &mut Kernel) -> Result<ComplexPrelude, KernelError> {
    let creal = build_creal_prelude(kernel)?;
    let prelude = intern_names(kernel, creal);
    if kernel.environment().get(prelude.complex).is_some() {
        return Ok(prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<(), KernelError> {
        let mut d = IntDev::new(kernel, creal.rat.int);
        declare_carrier(&mut d, prelude)?;
        declare_projections(&mut d, prelude)?;
        declare_equiv(&mut d, prelude)?;
        declare_setoid_laws(&mut d, prelude)?;
        declare_constants(&mut d, prelude)?;
        declare_operations(&mut d, prelude)?;
        declare_congruences(&mut d, prelude)?;
        declare_projection_congruences(&mut d, prelude)?;
        declare_ring_laws(&mut d, prelude)?;
        declare_pinning(&mut d, prelude)?;
        declare_re_add_im(&mut d, prelude)?;
        declare_conj_laws(&mut d, prelude)?;
        declare_conj_sub_ofreal_i(&mut d, prelude)?;
        declare_eq_conj_iff_real(&mut d, prelude)?;
        declare_norm(&mut d, prelude)?;
        declare_norm_conjugation(&mut d, prelude)?;
        declare_norm_sq_eq_zero_of_eq_zero(&mut d, prelude)?;
        declare_eq_zero_of_norm_sq_eq_zero(&mut d, prelude)?;
        declare_norm_sq_eq_zero_iff(&mut d, prelude)?;
        declare_norm_sq_add(&mut d, prelude)?;
        declare_no_order(&mut d, prelude)?;
        declare_inv(&mut d, prelude)?;
        declare_complex_mul_inv_cancel(&mut d, prelude)?;
        declare_complex_inv_congr(&mut d, prelude)?;
        declare_div(&mut d, prelude)?;
        declare_div_self(&mut d, prelude)?;
        declare_apart(&mut d, prelude)?;
        declare_apart_irrefl(&mut d, prelude)?;
        declare_apart_symm(&mut d, prelude)?;
        declare_apart_of_normsq_pos(&mut d, prelude)?;
        declare_mul_apart_zero(&mut d, prelude)?;
        declare_mul_eq_zero_not_both_apart_zero(&mut d, prelude)?;
        declare_complex_inv_mul_cancel(&mut d, prelude)?;
        declare_pos_bound_conj(&mut d, prelude)?;
        declare_conj_inv(&mut d, prelude)?;
        declare_pow(&mut d, prelude)?;
        declare_pow_equations(&mut d, prelude)?;
        declare_pow_add(&mut d, prelude)?;
        declare_norm_sq_pow(&mut d, prelude)?;
        declare_sum_range(&mut d, prelude)?;
        declare_sum_range_equations(&mut d, prelude)?;
        declare_sum_range_congr(&mut d, prelude)?;
        declare_mul_sum_range(&mut d, prelude)?;
        declare_mul_sub_one_geom(&mut d, prelude)?;
        declare_geom_series_div(&mut d, prelude)?;
        declare_of_nat(&mut d, prelude)?;
        declare_of_nat_equations(&mut d, prelude)?;
        declare_of_nat_add(&mut d, prelude)?;
        declare_of_nat_mul(&mut d, prelude)?;
        declare_sum_range_add(&mut d, prelude)?;
        declare_sum_range_shift_front(&mut d, prelude)?;
        declare_sum_range_congr_lt(&mut d, prelude)?;
        declare_sum_range_split(&mut d, prelude)?;
        declare_add_pow(&mut d, prelude)?;
        declare_is_root_of_unity(&mut d, prelude)?;
        declare_one_is_root_of_unity(&mut d, prelude)?;
        declare_i_is_fourth_root(&mut d, prelude)?;
        declare_pow_mul(&mut d, prelude)?;
        declare_geom_sum_eq_zero_of_root_of_unity(&mut d, prelude)?;
        declare_root_of_unity_mul(&mut d, prelude)?;
        declare_root_of_unity_pow(&mut d, prelude)
    })();
    match built {
        Ok(()) => Ok(prelude),
        Err(error) => {
            kernel.rollback_prelude(checkpoint);
            Err(error)
        }
    }
}

// --- term builders ----------------------------------------------------------

/// `Complex`.
fn complex_ty(d: &mut IntDev<'_>, p: ComplexPrelude) -> ExprId {
    d.kernel().const_(p.complex, vec![])
}

/// `CReal`.
fn creal_ty(d: &mut IntDev<'_>, p: ComplexPrelude) -> ExprId {
    d.kernel().const_(p.creal.creal, vec![])
}

/// `Complex.re z`.
fn re_of(d: &mut IntDev<'_>, p: ComplexPrelude, z: ExprId) -> ExprId {
    d.const_app(p.re, &[z])
}

/// `Complex.im z`.
fn im_of(d: &mut IntDev<'_>, p: ComplexPrelude, z: ExprId) -> ExprId {
    d.const_app(p.im, &[z])
}

/// `Complex.Equiv z w`.
fn zeq(d: &mut IntDev<'_>, p: ComplexPrelude, z: ExprId, w: ExprId) -> ExprId {
    d.const_app(p.equiv, &[z, w])
}

/// `And.intro` at two `Prop`s.
fn and_intro(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    left: ExprId,
    right: ExprId,
    lp: ExprId,
    rp: ExprId,
) -> ExprId {
    let intro = p.creal.rat.int.logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

/// A symbolic complex expression, in the language every law below is written
/// in.
///
/// The point of the type is [`parts`]: a `CExpr` knows its own real and
/// imaginary parts as [`RExpr`]s, so a `Complex` law becomes two `CReal` ring
/// identities mechanically rather than by hand.
#[derive(Clone)]
enum CExpr {
    /// A `Complex` variable, carrying its term and its two projections.
    Var(ExprId, ExprId, ExprId),
    /// `Complex.zero`.
    Zero,
    /// `Complex.one`.
    One,
    /// `Complex.I`.
    I,
    /// `Complex.ofReal`, of a real expression.
    OfReal(RExpr, ExprId),
    /// `Complex.add`.
    Add(Box<CExpr>, Box<CExpr>),
    /// `Complex.neg`.
    Neg(Box<CExpr>),
    /// `Complex.mul`.
    Mul(Box<CExpr>, Box<CExpr>),
    /// `Complex.conj`.
    Conj(Box<CExpr>),
}

impl CExpr {
    fn var(d: &mut IntDev<'_>, p: ComplexPrelude, z: ExprId) -> CExpr {
        let re = re_of(d, p, z);
        let im = im_of(d, p, z);
        CExpr::Var(z, re, im)
    }
    fn add(a: CExpr, b: CExpr) -> CExpr {
        CExpr::Add(Box::new(a), Box::new(b))
    }
    fn mul(a: CExpr, b: CExpr) -> CExpr {
        CExpr::Mul(Box::new(a), Box::new(b))
    }
    fn neg(a: CExpr) -> CExpr {
        CExpr::Neg(Box::new(a))
    }
    fn conj(a: CExpr) -> CExpr {
        CExpr::Conj(Box::new(a))
    }
}

/// The real and imaginary parts of a symbolic complex expression, as `CReal`
/// expressions the ring calculus can decide.
///
/// This *is* the definition of each operation, transcribed once. `Mul` is the
/// only clause that mixes the components.
fn parts(e: &CExpr) -> (RExpr, RExpr) {
    match e {
        CExpr::Var(_, re, im) => (RExpr::Atom(*re), RExpr::Atom(*im)),
        CExpr::Zero => (RExpr::Zero, RExpr::Zero),
        CExpr::One => (RExpr::One, RExpr::Zero),
        CExpr::I => (RExpr::Zero, RExpr::One),
        CExpr::OfReal(r, _) => (r.clone(), RExpr::Zero),
        CExpr::Add(a, b) => {
            let (ar, ai) = parts(a);
            let (br, bi) = parts(b);
            (RExpr::add(ar, br), RExpr::add(ai, bi))
        }
        CExpr::Neg(a) => {
            let (ar, ai) = parts(a);
            (RExpr::neg(ar), RExpr::neg(ai))
        }
        CExpr::Mul(a, b) => {
            let (ar, ai) = parts(a);
            let (br, bi) = parts(b);
            (
                RExpr::add(
                    RExpr::mul(ar.clone(), br.clone()),
                    RExpr::neg(RExpr::mul(ai.clone(), bi.clone())),
                ),
                RExpr::add(RExpr::mul(ar, bi), RExpr::mul(ai, br)),
            )
        }
        CExpr::Conj(a) => {
            let (ar, ai) = parts(a);
            (ar, RExpr::neg(ai))
        }
    }
}

/// The `Complex` term a symbolic expression denotes.
fn render_c(d: &mut IntDev<'_>, p: ComplexPrelude, e: &CExpr) -> ExprId {
    match e {
        CExpr::Var(z, _, _) => *z,
        CExpr::Zero => d.kernel().const_(p.zero, vec![]),
        CExpr::One => d.kernel().const_(p.one, vec![]),
        CExpr::I => d.kernel().const_(p.i, vec![]),
        CExpr::OfReal(_, term) => d.const_app(p.of_real, &[*term]),
        CExpr::Add(a, b) => {
            let left = render_c(d, p, a);
            let right = render_c(d, p, b);
            d.const_app(p.add, &[left, right])
        }
        CExpr::Neg(a) => {
            let inner = render_c(d, p, a);
            d.const_app(p.neg, &[inner])
        }
        CExpr::Mul(a, b) => {
            let left = render_c(d, p, a);
            let right = render_c(d, p, b);
            d.const_app(p.mul, &[left, right])
        }
        CExpr::Conj(a) => {
            let inner = render_c(d, p, a);
            d.const_app(p.conj, &[inner])
        }
    }
}

/// The `And.intro` proof of `Complex.Equiv lhs rhs`, both components decided by
/// the ring calculus.
///
/// The proof's *type* is the reduced, componentwise one; the kernel accepts it
/// against the `Complex.Equiv` statement by δι-reduction, which is exactly the
/// property that makes the pair carrier worth having.
fn ring_law_proof(d: &mut IntDev<'_>, p: ComplexPrelude, lhs: &CExpr, rhs: &CExpr) -> ExprId {
    let creal = p.creal;
    let (lr, li) = parts(lhs);
    let (rr, ri) = parts(rhs);
    let real_proof = ring_proof(d, creal, &lr, &rr);
    let imag_proof = ring_proof(d, creal, &li, &ri);
    let lr_term = ring::render(d, creal, &lr);
    let rr_term = ring::render(d, creal, &rr);
    let li_term = ring::render(d, creal, &li);
    let ri_term = ring::render(d, creal, &ri);
    let real_claim = ceq(d, creal, lr_term, rr_term);
    let imag_claim = ceq(d, creal, li_term, ri_term);
    and_intro(d, p, real_claim, imag_claim, real_proof, imag_proof)
}

// --- the carrier ------------------------------------------------------------

/// `Complex`, a one-constructor inductive in `Type 0` with two `CReal` fields.
fn declare_carrier(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let real = creal_ty(d, p);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);
    let result = complex_ty(d, p);
    let mk_ty = {
        let inner = d.arrow(real, result);
        d.arrow(real, inner)
    };
    d.kernel()
        .add_inductive(p.complex, &[], 0, type0, &[(p.mk, mk_ty)])
}

/// The two projections, by large elimination out of the `Type`-valued
/// inductive.
fn declare_projections(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let real = creal_ty(d, p);
    let carrier = complex_ty(d, p);
    let one = d.level_one();
    let anon = d.anon_name();

    let project = |d: &mut IntDev<'_>, name: NameId, first: bool| -> Result<(), KernelError> {
        let motive = d.kernel().lam(anon, carrier, real, BinderInfo::Default);
        let minor = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let chosen = if first { a } else { b };
            let inner = d.lam_fv(b_fv, real, chosen);
            d.lam_fv(a_fv, real, inner)
        };
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, z]);
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = d.arrow(carrier, real);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(LEAF_HEIGHT),
        })
    };
    project(d, p.re, true)?;
    project(d, p.im, false)
}

/// `Complex.Equiv z w := CReal.Equiv (re z) (re w) ∧ CReal.Equiv (im z) (im w)`.
fn declare_equiv(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let prop = d.kernel().sort_zero();
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let re_z = re_of(d, p, z);
    let re_w = re_of(d, p, w);
    let im_z = im_of(d, p, z);
    let im_w = im_of(d, p, w);
    let left = ceq(d, p.creal, re_z, re_w);
    let right = ceq(d, p.creal, im_z, im_w);
    let body = d.and(left, right);
    let value = {
        let with_w = d.lam_fv(w_fv, carrier, body);
        d.lam_fv(z_fv, carrier, with_w)
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
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })
}

/// The two component `CReal.Equiv` propositions of `Complex.Equiv z w`, and the
/// two halves of a proof of it.
fn equiv_halves(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    z: ExprId,
    w: ExprId,
    proof: ExprId,
) -> (ExprId, ExprId) {
    let re_z = re_of(d, p, z);
    let re_w = re_of(d, p, w);
    let im_z = im_of(d, p, z);
    let im_w = im_of(d, p, w);
    let left = ceq(d, p.creal, re_z, re_w);
    let right = ceq(d, p.creal, im_z, im_w);
    let first = d.and_left(left, right, proof);
    let second = d.and_right(left, right, proof);
    (first, second)
}

/// `Equiv.refl`, `Equiv.symm`, `Equiv.trans`: componentwise, and nothing more.
fn declare_setoid_laws(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    // refl
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let re_z = re_of(d, p, z);
        let im_z = im_of(d, p, z);
        let left = ceq(d, creal, re_z, re_z);
        let right = ceq(d, creal, im_z, im_z);
        let lp = crefl(d, creal, re_z);
        let rp = crefl(d, creal, im_z);
        let body = and_intro(d, p, left, right, lp, rp);
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = {
            let claim = zeq(d, p, z, z);
            d.pi_fv(z_fv, carrier, claim)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.equiv_refl,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // symm
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let hypothesis = zeq(d, p, z, w);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let (first, second) = equiv_halves(d, p, z, w, h);
        let re_z = re_of(d, p, z);
        let re_w = re_of(d, p, w);
        let im_z = im_of(d, p, z);
        let im_w = im_of(d, p, w);
        let lp = d.lemma(creal.equiv_symm, &[re_z, re_w, first]);
        let rp = d.lemma(creal.equiv_symm, &[im_z, im_w, second]);
        let left = ceq(d, creal, re_w, re_z);
        let right = ceq(d, creal, im_w, im_z);
        let body = and_intro(d, p, left, right, lp, rp);
        let value = {
            let with_h = d.lam_fv(h_fv, hypothesis, body);
            let with_w = d.lam_fv(w_fv, carrier, with_h);
            d.lam_fv(z_fv, carrier, with_w)
        };
        let ty = {
            let conclusion = zeq(d, p, w, z);
            let inner = d.arrow(hypothesis, conclusion);
            let with_w = d.pi_fv(w_fv, carrier, inner);
            d.pi_fv(z_fv, carrier, with_w)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.equiv_symm,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // trans
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let first_ty = zeq(d, p, z, w);
        let second_ty = zeq(d, p, w, v);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let (a1, b1) = equiv_halves(d, p, z, w, h1);
        let (a2, b2) = equiv_halves(d, p, w, v, h2);
        let re_z = re_of(d, p, z);
        let re_w = re_of(d, p, w);
        let re_v = re_of(d, p, v);
        let im_z = im_of(d, p, z);
        let im_w = im_of(d, p, w);
        let im_v = im_of(d, p, v);
        let lp = d.lemma(creal.equiv_trans, &[re_z, re_w, re_v, a1, a2]);
        let rp = d.lemma(creal.equiv_trans, &[im_z, im_w, im_v, b1, b2]);
        let left = ceq(d, creal, re_z, re_v);
        let right = ceq(d, creal, im_z, im_v);
        let body = and_intro(d, p, left, right, lp, rp);
        let value = {
            let with2 = d.lam_fv(h2_fv, second_ty, body);
            let with1 = d.lam_fv(h1_fv, first_ty, with2);
            let with_v = d.lam_fv(v_fv, carrier, with1);
            let with_w = d.lam_fv(w_fv, carrier, with_v);
            d.lam_fv(z_fv, carrier, with_w)
        };
        let ty = {
            let conclusion = zeq(d, p, z, v);
            let after2 = d.arrow(second_ty, conclusion);
            let after1 = d.arrow(first_ty, after2);
            let with_v = d.pi_fv(v_fv, carrier, after1);
            let with_w = d.pi_fv(w_fv, carrier, with_v);
            d.pi_fv(z_fv, carrier, with_w)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.equiv_trans,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `ofReal`, `zero`, `one`, `I`.
fn declare_constants(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let real = creal_ty(d, p);
    let carrier = complex_ty(d, p);

    // ofReal r := mk r CReal.zero
    {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let zero = czero(d, creal);
        let constructor = d.kernel().const_(p.mk, vec![]);
        let body = d.apply(constructor, &[r, zero]);
        let value = d.lam_fv(r_fv, real, body);
        let ty = d.arrow(real, carrier);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.of_real,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 1),
        })?;
    }

    let constant = |d: &mut IntDev<'_>, name: NameId, real_part: ExprId, imag_part: ExprId| {
        let constructor = d.kernel().const_(p.mk, vec![]);
        let value = d.apply(constructor, &[real_part, imag_part]);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty: carrier,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 2),
        })
    };
    let zero = czero(d, creal);
    let one = cone(d, creal);
    constant(d, p.zero, zero, zero)?;
    constant(d, p.one, one, zero)?;
    constant(d, p.i, zero, one)
}

/// `add`, `neg`, `mul`, `conj`, `normSq`.
fn declare_operations(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let real = creal_ty(d, p);

    let binary =
        |d: &mut IntDev<'_>,
         name: NameId,
         combine: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId, ExprId) -> (ExprId, ExprId)|
         -> Result<(), KernelError> {
            let z_fv = d.fresh_fvar();
            let z = d.kernel().fvar(z_fv);
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let a = re_of(d, p, z);
            let b = im_of(d, p, z);
            let c = re_of(d, p, w);
            let e = im_of(d, p, w);
            let (real_part, imag_part) = combine(d, a, b, c, e);
            let constructor = d.kernel().const_(p.mk, vec![]);
            let body = d.apply(constructor, &[real_part, imag_part]);
            let value = {
                let with_w = d.lam_fv(w_fv, carrier, body);
                d.lam_fv(z_fv, carrier, with_w)
            };
            let ty = {
                let inner = d.arrow(carrier, carrier);
                d.arrow(carrier, inner)
            };
            d.kernel().add_declaration(Declaration::Definition {
                name,
                uparams: vec![],
                ty,
                value,
                hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 3),
            })
        };

    binary(d, p.add, &|d, a, b, c, e| {
        let real_part = cadd(d, creal, a, c);
        let imag_part = cadd(d, creal, b, e);
        (real_part, imag_part)
    })?;
    binary(d, p.mul, &|d, a, b, c, e| {
        let ac = cmul(d, creal, a, c);
        let be = cmul(d, creal, b, e);
        let negated = cneg(d, creal, be);
        let real_part = cadd(d, creal, ac, negated);
        let ae = cmul(d, creal, a, e);
        let bc = cmul(d, creal, b, c);
        let imag_part = cadd(d, creal, ae, bc);
        (real_part, imag_part)
    })?;

    let unary = |d: &mut IntDev<'_>,
                 name: NameId,
                 combine: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> (ExprId, ExprId)|
     -> Result<(), KernelError> {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let (real_part, imag_part) = combine(d, a, b);
        let constructor = d.kernel().const_(p.mk, vec![]);
        let body = d.apply(constructor, &[real_part, imag_part]);
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = d.arrow(carrier, carrier);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 3),
        })
    };
    unary(d, p.neg, &|d, a, b| {
        let real_part = cneg(d, creal, a);
        let imag_part = cneg(d, creal, b);
        (real_part, imag_part)
    })?;
    unary(d, p.conj, &|d, a, b| {
        let imag_part = cneg(d, creal, b);
        (a, imag_part)
    })?;

    // normSq z := re z * re z + im z * im z, valued in CReal.
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let aa = cmul(d, creal, a, a);
        let bb = cmul(d, creal, b, b);
        let body = cadd(d, creal, aa, bb);
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = d.arrow(carrier, real);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.norm_sq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 4),
        })?;
    }
    Ok(())
}

/// The four setoid congruence obligations: `add`, `neg`, `mul`, `conj`.
///
/// None of them needs the ring calculus — each component of the conclusion is
/// the corresponding `CReal` congruence applied to the hypotheses' components.
/// `mul` is the one that mixes: its real part needs `mul_congr` twice and
/// `neg_congr` once, under `add_congr`.
fn declare_congruences(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    // A binary congruence, from the four component proofs.
    let binary = |d: &mut IntDev<'_>,
                  name: NameId,
                  op: NameId,
                  components: &dyn Fn(
        &mut IntDev<'_>,
        [ExprId; 4],
        [ExprId; 4],
        [ExprId; 4],
    ) -> (ExprId, ExprId, ExprId, ExprId)|
     -> Result<(), KernelError> {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let z2_fv = d.fresh_fvar();
        let z2 = d.kernel().fvar(z2_fv);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let w2_fv = d.fresh_fvar();
        let w2 = d.kernel().fvar(w2_fv);
        let first_ty = zeq(d, p, z, z2);
        let second_ty = zeq(d, p, w, w2);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let (za, zb) = equiv_halves(d, p, z, z2, h1);
        let (wa, wb) = equiv_halves(d, p, w, w2, h2);
        let left_parts = [
            re_of(d, p, z),
            im_of(d, p, z),
            re_of(d, p, w),
            im_of(d, p, w),
        ];
        let right_parts = [
            re_of(d, p, z2),
            im_of(d, p, z2),
            re_of(d, p, w2),
            im_of(d, p, w2),
        ];
        let (real_claim, imag_claim, real_proof, imag_proof) =
            components(d, left_parts, right_parts, [za, zb, wa, wb]);
        let body = and_intro(d, p, real_claim, imag_claim, real_proof, imag_proof);
        let value = {
            let with2 = d.lam_fv(h2_fv, second_ty, body);
            let with1 = d.lam_fv(h1_fv, first_ty, with2);
            let with_w2 = d.lam_fv(w2_fv, carrier, with1);
            let with_w = d.lam_fv(w_fv, carrier, with_w2);
            let with_z2 = d.lam_fv(z2_fv, carrier, with_w);
            d.lam_fv(z_fv, carrier, with_z2)
        };
        let ty = {
            let left = d.const_app(op, &[z, w]);
            let right = d.const_app(op, &[z2, w2]);
            let conclusion = zeq(d, p, left, right);
            let after2 = d.arrow(second_ty, conclusion);
            let after1 = d.arrow(first_ty, after2);
            let with_w2 = d.pi_fv(w2_fv, carrier, after1);
            let with_w = d.pi_fv(w_fv, carrier, with_w2);
            let with_z2 = d.pi_fv(z2_fv, carrier, with_w);
            d.pi_fv(z_fv, carrier, with_z2)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    };

    binary(d, p.add_congr, p.add, &|d, l, r, h| {
        let [a, b, c, e] = l;
        let [a2, b2, c2, e2] = r;
        let [ha, hb, hc, he] = h;
        let real_left = cadd(d, creal, a, c);
        let real_right = cadd(d, creal, a2, c2);
        let imag_left = cadd(d, creal, b, e);
        let imag_right = cadd(d, creal, b2, e2);
        let real_claim = ceq(d, creal, real_left, real_right);
        let imag_claim = ceq(d, creal, imag_left, imag_right);
        let real_proof = d.lemma(creal.add_congr, &[a, a2, c, c2, ha, hc]);
        let imag_proof = d.lemma(creal.add_congr, &[b, b2, e, e2, hb, he]);
        (real_claim, imag_claim, real_proof, imag_proof)
    })?;

    binary(d, p.mul_congr, p.mul, &|d, l, r, h| {
        let [a, b, c, e] = l;
        let [a2, b2, c2, e2] = r;
        let [ha, hb, hc, he] = h;
        // real: a·c + −(b·e)
        let ac = cmul(d, creal, a, c);
        let be = cmul(d, creal, b, e);
        let nbe = cneg(d, creal, be);
        let real_left = cadd(d, creal, ac, nbe);
        let ac2 = cmul(d, creal, a2, c2);
        let be2 = cmul(d, creal, b2, e2);
        let nbe2 = cneg(d, creal, be2);
        let real_right = cadd(d, creal, ac2, nbe2);
        let ac_proof = d.lemma(creal.mul_congr, &[a, a2, c, c2, ha, hc]);
        let be_proof = d.lemma(creal.mul_congr, &[b, b2, e, e2, hb, he]);
        let nbe_proof = d.lemma(creal.neg_congr, &[be, be2, be_proof]);
        let real_proof = d.lemma(creal.add_congr, &[ac, ac2, nbe, nbe2, ac_proof, nbe_proof]);
        // imag: a·e + b·c
        let ae = cmul(d, creal, a, e);
        let bc = cmul(d, creal, b, c);
        let imag_left = cadd(d, creal, ae, bc);
        let ae2 = cmul(d, creal, a2, e2);
        let bc2 = cmul(d, creal, b2, c2);
        let imag_right = cadd(d, creal, ae2, bc2);
        let ae_proof = d.lemma(creal.mul_congr, &[a, a2, e, e2, ha, he]);
        let bc_proof = d.lemma(creal.mul_congr, &[b, b2, c, c2, hb, hc]);
        let imag_proof = d.lemma(creal.add_congr, &[ae, ae2, bc, bc2, ae_proof, bc_proof]);
        let real_claim = ceq(d, creal, real_left, real_right);
        let imag_claim = ceq(d, creal, imag_left, imag_right);
        (real_claim, imag_claim, real_proof, imag_proof)
    })?;

    // The two unary congruences.
    let unary = |d: &mut IntDev<'_>,
                 name: NameId,
                 op: NameId,
                 negate_real: bool|
     -> Result<(), KernelError> {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let hypothesis = zeq(d, p, z, w);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let (first, second) = equiv_halves(d, p, z, w, h);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let a2 = re_of(d, p, w);
        let b2 = im_of(d, p, w);
        let nb = cneg(d, creal, b);
        let nb2 = cneg(d, creal, b2);
        let imag_proof = d.lemma(creal.neg_congr, &[b, b2, second]);
        let imag_claim = ceq(d, creal, nb, nb2);
        let (real_claim, real_proof) = if negate_real {
            let na = cneg(d, creal, a);
            let na2 = cneg(d, creal, a2);
            let proof = d.lemma(creal.neg_congr, &[a, a2, first]);
            let claim = ceq(d, creal, na, na2);
            (claim, proof)
        } else {
            let claim = ceq(d, creal, a, a2);
            (claim, first)
        };
        let body = and_intro(d, p, real_claim, imag_claim, real_proof, imag_proof);
        let value = {
            let with_h = d.lam_fv(h_fv, hypothesis, body);
            let with_w = d.lam_fv(w_fv, carrier, with_h);
            d.lam_fv(z_fv, carrier, with_w)
        };
        let ty = {
            let left = d.const_app(op, &[z]);
            let right = d.const_app(op, &[w]);
            let conclusion = zeq(d, p, left, right);
            let inner = d.arrow(hypothesis, conclusion);
            let with_w = d.pi_fv(w_fv, carrier, inner);
            d.pi_fv(z_fv, carrier, with_w)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    };
    unary(d, p.neg_congr, p.neg, true)?;
    unary(d, p.conj_congr, p.conj, false)
}

/// `re_congr`, `im_congr`: the two projections are congruences on
/// `Complex.Equiv`.
///
/// Immediate from [`equiv_halves`] — its two components already **are** these
/// propositions, so there is nothing left to derive.
fn declare_projection_congruences(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    let project = |d: &mut IntDev<'_>, name: NameId, real_half: bool| -> Result<(), KernelError> {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let hypothesis = zeq(d, p, z, w);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let (first, second) = equiv_halves(d, p, z, w, h);
        let chosen = if real_half { first } else { second };
        let value = {
            let with_h = d.lam_fv(h_fv, hypothesis, chosen);
            let with_w = d.lam_fv(w_fv, carrier, with_h);
            d.lam_fv(z_fv, carrier, with_w)
        };
        let ty = {
            let proj = if real_half { p.re } else { p.im };
            let left = d.const_app(proj, &[z]);
            let right = d.const_app(proj, &[w]);
            let conclusion = ceq(d, creal, left, right);
            let inner = d.arrow(hypothesis, conclusion);
            let with_w = d.pi_fv(w_fv, carrier, inner);
            d.pi_fv(z_fv, carrier, with_w)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    };
    project(d, p.re_congr, true)?;
    project(d, p.im_congr, false)
}

/// A universally-quantified `Complex.Equiv` law, `∀ vars, Equiv (lhs vars)
/// (rhs vars)`, decided by the ring calculus and declared as a `Theorem`.
///
/// Shared by [`declare_ring_laws`] and [`declare_conj_laws`]: both reduce a
/// `Complex` identity to two `CReal` ring obligations exactly this way, and
/// the only thing that differs between call sites is which `CExpr`s `build`
/// produces.
fn complex_law(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    name: NameId,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (CExpr, CExpr),
) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let fvars: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvars.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (lhs, rhs) = build(d, &vars);
    let body = ring_law_proof(d, p, &lhs, &rhs);
    let left = render_c(d, p, &lhs);
    let right = render_c(d, p, &rhs);
    let claim = zeq(d, p, left, right);
    let mut value = body;
    let mut ty = claim;
    for &f in fvars.iter().rev() {
        value = d.lam_fv(f, carrier, value);
        ty = d.pi_fv(f, carrier, ty);
    }
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// The nine commutative-ring laws, every one decided by the ring calculus.
fn declare_ring_laws(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    complex_law(d, p, p.add_comm, 2, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        (CExpr::add(z.clone(), w.clone()), CExpr::add(w, z))
    })?;
    complex_law(d, p, p.add_assoc, 3, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        let u = CExpr::var(d, p, v[2]);
        (
            CExpr::add(CExpr::add(z.clone(), w.clone()), u.clone()),
            CExpr::add(z, CExpr::add(w, u)),
        )
    })?;
    complex_law(d, p, p.add_zero, 1, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        (CExpr::add(z.clone(), CExpr::Zero), z)
    })?;
    complex_law(d, p, p.add_neg, 1, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        (CExpr::add(z.clone(), CExpr::neg(z)), CExpr::Zero)
    })?;
    complex_law(d, p, p.mul_comm, 2, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        (CExpr::mul(z.clone(), w.clone()), CExpr::mul(w, z))
    })?;
    complex_law(d, p, p.mul_assoc, 3, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        let u = CExpr::var(d, p, v[2]);
        (
            CExpr::mul(CExpr::mul(z.clone(), w.clone()), u.clone()),
            CExpr::mul(z, CExpr::mul(w, u)),
        )
    })?;
    complex_law(d, p, p.mul_one, 1, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        (CExpr::mul(z.clone(), CExpr::One), z)
    })?;
    complex_law(d, p, p.mul_zero, 1, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        (CExpr::mul(z, CExpr::Zero), CExpr::Zero)
    })?;
    complex_law(d, p, p.left_distrib, 3, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        let u = CExpr::var(d, p, v[2]);
        (
            CExpr::mul(z.clone(), CExpr::add(w.clone(), u.clone())),
            CExpr::add(CExpr::mul(z.clone(), w), CExpr::mul(z, u)),
        )
    })
}

/// `conj_conj`, `conj_add`, `conj_mul`: conjugation is an involutive ring
/// homomorphism.
///
/// Each is a `Complex.Equiv` identity over the *same* commutative-ring
/// calculus as [`declare_ring_laws`] — `CExpr::Conj` is already a case of
/// [`parts`], so nothing new is needed to decide any of the three.
fn declare_conj_laws(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    complex_law(d, p, p.conj_conj, 1, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        (CExpr::conj(CExpr::conj(z.clone())), z)
    })?;
    complex_law(d, p, p.conj_add, 2, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        (
            CExpr::conj(CExpr::add(z.clone(), w.clone())),
            CExpr::add(CExpr::conj(z), CExpr::conj(w)),
        )
    })?;
    complex_law(d, p, p.conj_mul, 2, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        (
            CExpr::conj(CExpr::mul(z.clone(), w.clone())),
            CExpr::mul(CExpr::conj(z), CExpr::conj(w)),
        )
    })
}

/// `conj_sub`, `conj_ofReal`, `conj_I`: three more corollaries of the same
/// ring calculus [`declare_conj_laws`] already uses.
fn declare_conj_sub_ofreal_i(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let real = creal_ty(d, p);

    complex_law(d, p, p.conj_sub, 2, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let w = CExpr::var(d, p, v[1]);
        (
            CExpr::conj(CExpr::add(z.clone(), CExpr::neg(w.clone()))),
            CExpr::add(CExpr::conj(z), CExpr::neg(CExpr::conj(w))),
        )
    })?;

    // conj_ofReal : Equiv (conj (ofReal r)) (ofReal r)
    {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let lhs = CExpr::conj(CExpr::OfReal(RExpr::Atom(r), r));
        let rhs = CExpr::OfReal(RExpr::Atom(r), r);
        let body = ring_law_proof(d, p, &lhs, &rhs);
        let left = render_c(d, p, &lhs);
        let right = render_c(d, p, &rhs);
        let claim = zeq(d, p, left, right);
        let value = d.lam_fv(r_fv, real, body);
        let ty = d.pi_fv(r_fv, real, claim);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.conj_of_real,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // conj_I : Equiv (conj I) (neg I)
    {
        let lhs = CExpr::conj(CExpr::I);
        let rhs = CExpr::neg(CExpr::I);
        let value = ring_law_proof(d, p, &lhs, &rhs);
        let left = render_c(d, p, &lhs);
        let right = render_c(d, p, &rhs);
        let ty = zeq(d, p, left, right);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.conj_i,
            uparams: vec![],
            ty,
            value,
        })
    }
}

/// From `hyp : CReal.Equiv (CReal.add x x) CReal.zero`, conclude
/// `CReal.Equiv x CReal.zero` — ℝ has no 2-torsion.
///
/// Not an algebraic rearrangement: `x + x ~ 0` does not entail `x ~ 0` in an
/// arbitrary commutative ring (characteristic 2 is a counterexample), so this
/// genuinely uses that `2 := CReal.add CReal.one CReal.one` is **positive**
/// (hence invertible via [`CRealPrelude::inv`]) — proved from
/// `CReal.zero_lt_one` and `CReal.add_lt_add_of_le_of_lt`, not assumed. No
/// classical reasoning: the modulus `k` separating `two` from `0` is extracted
/// from `CReal.pos_bound_of_lt`'s `Exists` by [`exists_elim`], exactly
/// `CReal.PosBound`'s own convention.
fn double_zero_imp_zero(d: &mut IntDev<'_>, p: ComplexPrelude, x: ExprId, hyp: ExprId) -> ExprId {
    let creal = p.creal;
    let nat = d.nat_ty();
    let zero = czero(d, creal);
    let one = cone(d, creal);
    let two = cadd(d, creal, one, one);

    // 0 < two, from 0 ≤ 1 and 0 < 1 shifted by `add_lt_add_of_le_of_lt`.
    let zero_lt_one = d.kernel().const_(creal.zero_lt_one, vec![]);
    let le_zero_one = d.lemma(creal.le_of_lt, &[zero, one, zero_lt_one]);
    let sum_lt = d.lemma(
        creal.add_lt_add_of_le_of_lt,
        &[zero, one, zero, one, le_zero_one, zero_lt_one],
    );
    let zero_zero = cadd(d, creal, zero, zero);
    let add_zero_zero = d.lemma(creal.add_zero, &[zero]);
    let two_refl = crefl(d, creal, two);
    let lt_zero_two = d.lemma(
        creal.lt_congr,
        &[zero_zero, zero, two, two, add_zero_zero, two_refl, sum_lt],
    );

    // two * x ~ x + x, a pure ring identity once `two` is read as `1 + 1`.
    let two_x = cmul(d, creal, two, x);
    let xx = cadd(d, creal, x, x);
    let two_x_eq_xx = ring_proof(
        d,
        creal,
        &RExpr::mul(RExpr::add(RExpr::One, RExpr::One), RExpr::Atom(x)),
        &RExpr::add(RExpr::Atom(x), RExpr::Atom(x)),
    );
    let two_x_eq_zero = ctrans(d, creal, two_x, xx, zero, two_x_eq_xx, hyp);

    // ∃ k, PosBound two k.
    let k_fv = d.fresh_fvar();
    let k_var = d.kernel().fvar(k_fv);
    let pos_bound_template = d.const_app(creal.pos_bound, &[two, k_var]);
    let predicate = d.lam_fv(k_fv, nat, pos_bound_template);
    let witness = d.const_app(creal.pos_bound_of_lt, &[two, lt_zero_two]);

    let target = ceq(d, creal, x, zero);

    let minor = {
        let k2_fv = d.fresh_fvar();
        let k2 = d.kernel().fvar(k2_fv);
        let h_ty = d.const_app(creal.pos_bound, &[two, k2]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let inv_two = d.const_app(creal.inv, &[two, k2, h]);
        let cancel = d.lemma(creal.mul_inv_cancel, &[two, k2, h]);

        let inv_two_refl = crefl(d, creal, inv_two);
        let prod_congr = d.lemma(
            creal.mul_congr,
            &[inv_two, inv_two, two_x, zero, inv_two_refl, two_x_eq_zero],
        );

        let inv_two_two = cmul(d, creal, inv_two, two);
        let inv_two_two_x = cmul(d, creal, inv_two_two, x);
        let inv_two_two_x_swapped = cmul(d, creal, inv_two, two_x);
        let assoc_fwd = d.lemma(creal.mul_assoc, &[inv_two, two, x]);
        let step1 = csymm(d, creal, inv_two_two_x, inv_two_two_x_swapped, assoc_fwd);

        let two_inv_two = cmul(d, creal, two, inv_two);
        let mc = d.lemma(creal.mul_comm, &[inv_two, two]);
        let combined = ctrans(d, creal, inv_two_two, two_inv_two, one, mc, cancel);

        let x_refl = crefl(d, creal, x);
        let one_x = cmul(d, creal, one, x);
        let step3 = d.lemma(creal.mul_congr, &[inv_two_two, one, x, x, combined, x_refl]);

        let x_one = cmul(d, creal, x, one);
        let mc2 = d.lemma(creal.mul_comm, &[one, x]);
        let mo = d.lemma(creal.mul_one, &[x]);
        let step4 = ctrans(d, creal, one_x, x_one, x, mc2, mo);

        let step34 = ctrans(d, creal, inv_two_two_x, one_x, x, step3, step4);
        let lhs_to_x = ctrans(
            d,
            creal,
            inv_two_two_x_swapped,
            inv_two_two_x,
            x,
            step1,
            step34,
        );

        let rhs_to_zero = d.lemma(creal.mul_zero, &[inv_two]);
        let inv_two_zero = cmul(d, creal, inv_two, zero);
        let x_to_swapped = csymm(d, creal, inv_two_two_x_swapped, x, lhs_to_x);

        let (_, final_proof) = cchain(
            d,
            creal,
            x,
            &[
                (inv_two_two_x_swapped, x_to_swapped),
                (inv_two_zero, prod_congr),
                (zero, rhs_to_zero),
            ],
        );

        let with_h = d.lam_fv(h_fv, h_ty, final_proof);
        d.lam_fv(k2_fv, nat, with_h)
    };

    exists_elim(d, predicate, target, witness, minor)
}

/// `Complex.eq_conj_iff_real`: `z` is real exactly when it equals its own
/// conjugate.
///
/// Both directions turn on the same fact about the *imaginary* half: `im
/// (conj z)` unfolds (one delta step on `conj`, one iota step over `mk`) to
/// `CReal.neg (im z)`, so the imaginary component of `z ~ conj z` **is**, up
/// to that reduction, `im z ~ CReal.neg (im z)`. The real component is free
/// either way — `re (conj z)` unfolds to `re z`, so `Equiv.refl` closes it
/// regardless of direction.
///
/// The forward direction still needs real work: `im z ~ neg (im z)` only gives
/// `im z ~ CReal.zero` once ℝ is known to have no 2-torsion, which
/// [`double_zero_imp_zero`] proves rather than assumes.
fn declare_eq_conj_iff_real(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let logic = creal.rat.int.logic;
    let carrier = complex_ty(d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let conj_z = d.const_app(p.conj, &[z]);
    let re_z = re_of(d, p, z);
    let im_z = im_of(d, p, z);
    let zero = czero(d, creal);

    let equiv_stmt = zeq(d, p, z, conj_z);
    let real_stmt = ceq(d, creal, im_z, zero);

    // mp : Equiv z (conj z) -> CReal.Equiv (im z) CReal.zero
    let mp_body = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let (_, second) = equiv_halves(d, p, z, conj_z, h);
        // `second : Equiv (im z) (im (conj z))`, defeq to `Equiv (im z) (neg (im z))`.
        let im_refl = crefl(d, creal, im_z);
        let neg_im = cneg(d, creal, im_z);
        let doubled = d.lemma(
            creal.add_congr,
            &[im_z, im_z, im_z, neg_im, im_refl, second],
        );
        // doubled : Equiv (add im_z im_z) (add im_z (neg im_z))
        let cancel = d.lemma(creal.add_neg, &[im_z]);
        // cancel : Equiv (add im_z (neg im_z)) zero
        let im_z_im_z = cadd(d, creal, im_z, im_z);
        let im_z_neg_im = cadd(d, creal, im_z, neg_im);
        let sum_zero = ctrans(d, creal, im_z_im_z, im_z_neg_im, zero, doubled, cancel);
        let proof = double_zero_imp_zero(d, p, im_z, sum_zero);
        d.lam_fv(h_fv, equiv_stmt, proof)
    };

    // mpr : CReal.Equiv (im z) CReal.zero -> Equiv z (conj z)
    let mpr_body = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let re_conj = re_of(d, p, conj_z);
        let im_conj = im_of(d, p, conj_z);
        let real_claim = ceq(d, creal, re_z, re_conj);
        let imag_claim = ceq(d, creal, im_z, im_conj);
        let real_proof = crefl(d, creal, re_z);
        // imag_proof : Equiv (im z) (neg (im z)), defeq to `Equiv (im z) (im (conj z))`.
        let neg_im = cneg(d, creal, im_z);
        let neg_congr_proof = d.lemma(creal.neg_congr, &[im_z, zero, h]);
        // neg_congr_proof : Equiv (neg im_z) (neg zero)
        let neg_zero_eq_zero = ring_proof(d, creal, &RExpr::neg(RExpr::Zero), &RExpr::Zero);
        let neg_zero = cneg(d, creal, zero);
        let neg_im_zero = ctrans(
            d,
            creal,
            neg_im,
            neg_zero,
            zero,
            neg_congr_proof,
            neg_zero_eq_zero,
        );
        let zero_to_neg_im = csymm(d, creal, neg_im, zero, neg_im_zero);
        let imag_proof = ctrans(d, creal, im_z, zero, neg_im, h, zero_to_neg_im);
        let body = and_intro(d, p, real_claim, imag_claim, real_proof, imag_proof);
        d.lam_fv(h_fv, real_stmt, body)
    };

    let iff_stmt = d.const_app(logic.iff, &[equiv_stmt, real_stmt]);
    let iff_proof = d.const_app(logic.iff_intro, &[equiv_stmt, real_stmt, mp_body, mpr_body]);

    let value = d.lam_fv(z_fv, carrier, iff_proof);
    let ty = d.pi_fv(z_fv, carrier, iff_stmt);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.eq_conj_iff_real,
        uparams: vec![],
        ty,
        value,
    })
}

/// The witnesses that pin the operations down, and the two that keep `Equiv`
/// from being the total relation.
fn declare_pinning(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let real = creal_ty(d, p);

    // ofReal_add and ofReal_mul: the embedding is a ring homomorphism.
    let embedding =
        |d: &mut IntDev<'_>, name: NameId, multiplicative: bool| -> Result<(), KernelError> {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let combined = if multiplicative {
                cmul(d, creal, a, b)
            } else {
                cadd(d, creal, a, b)
            };
            let left = CExpr::OfReal(RExpr::Atom(a), a);
            let right = CExpr::OfReal(RExpr::Atom(b), b);
            let lhs = if multiplicative {
                CExpr::mul(left, right)
            } else {
                CExpr::add(left, right)
            };
            let combined_expr = if multiplicative {
                RExpr::mul(RExpr::Atom(a), RExpr::Atom(b))
            } else {
                RExpr::add(RExpr::Atom(a), RExpr::Atom(b))
            };
            let rhs = CExpr::OfReal(combined_expr, combined);
            let body = ring_law_proof(d, p, &lhs, &rhs);
            let left_term = render_c(d, p, &lhs);
            let right_term = render_c(d, p, &rhs);
            let claim = zeq(d, p, left_term, right_term);
            let value = {
                let with_b = d.lam_fv(b_fv, real, body);
                d.lam_fv(a_fv, real, with_b)
            };
            let ty = {
                let with_b = d.pi_fv(b_fv, real, claim);
                d.pi_fv(a_fv, real, with_b)
            };
            d.kernel().add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
        };
    embedding(d, p.of_real_add, false)?;
    embedding(d, p.of_real_mul, true)?;

    // I_sq : Equiv (mul I I) (neg one)
    {
        let lhs = CExpr::mul(CExpr::I, CExpr::I);
        let rhs = CExpr::neg(CExpr::One);
        let value = ring_law_proof(d, p, &lhs, &rhs);
        let left = render_c(d, p, &lhs);
        let right = render_c(d, p, &rhs);
        let ty = zeq(d, p, left, right);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.i_sq,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // The two discrimination witnesses, each a projection of CReal's.
    let discriminate = |d: &mut IntDev<'_>,
                        name: NameId,
                        other: NameId,
                        real_half: bool|
     -> Result<(), KernelError> {
        let zero = d.kernel().const_(p.zero, vec![]);
        let target = d.kernel().const_(other, vec![]);
        let hypothesis = zeq(d, p, zero, target);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let (first, second) = equiv_halves(d, p, zero, target, h);
        let chosen = if real_half { first } else { second };
        let refutation = d.kernel().const_(creal.not_zero_one, vec![]);
        let body = d.kernel().app(refutation, chosen);
        let value = d.lam_fv(h_fv, hypothesis, body);
        let ty = d.not(hypothesis);
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    };
    discriminate(d, p.not_zero_one, p.one, true)?;
    discriminate(d, p.not_zero_i, p.i, false)
}

/// `Complex.re_add_im : ∀ z, Equiv z (add (ofReal (re z)) (mul I (ofReal (im
/// z))))` — ℂ **is** ℝ², the reconstruction of `z` from its own two real
/// projections.
///
/// Decided by the same ring calculus as every law above: [`parts`] already
/// knows how `ofReal` and `I` unfold, so the right-hand side's components are
/// `(re z, 0)` and `(0, im z)`, and `add` finishes the arithmetic to exactly
/// `(re z, im z)` — `z`'s own components.
fn declare_re_add_im(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    complex_law(d, p, p.re_add_im, 1, &|d, v| {
        let z = CExpr::var(d, p, v[0]);
        let (re_z, im_z) = match &z {
            CExpr::Var(_, re, im) => (*re, *im),
            _ => unreachable!("CExpr::var always produces CExpr::Var"),
        };
        let real_part = CExpr::OfReal(RExpr::Atom(re_z), re_z);
        let imag_part = CExpr::OfReal(RExpr::Atom(im_z), im_z);
        let rhs = CExpr::add(real_part, CExpr::mul(CExpr::I, imag_part));
        (z, rhs)
    })
}

/// `mul_conj` and `normSq_nonneg`: the norm, and where it lands.
fn declare_norm(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    // mul_conj : Equiv (mul z (conj z)) (ofReal (normSq z))
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let var = CExpr::var(d, p, z);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let norm = d.const_app(p.norm_sq, &[z]);
        let lhs = CExpr::mul(var.clone(), CExpr::conj(var));
        let unfolded = RExpr::add(
            RExpr::mul(RExpr::Atom(a), RExpr::Atom(a)),
            RExpr::mul(RExpr::Atom(b), RExpr::Atom(b)),
        );
        let rhs = CExpr::OfReal(unfolded, norm);
        let body = ring_law_proof(d, p, &lhs, &rhs);
        let left = render_c(d, p, &lhs);
        let right = render_c(d, p, &rhs);
        let claim = zeq(d, p, left, right);
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = d.pi_fv(z_fv, carrier, claim);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.mul_conj,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // normSq_nonneg : CReal.le CReal.zero (normSq z)
    //
    // `sq_nonneg` twice, `add_le_add` once, and one `le_congr` to read
    // `0 + 0` as `0` -- ADR-0512's order laws, used verbatim.
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let zero = czero(d, creal);
        let aa = cmul(d, creal, a, a);
        let bb = cmul(d, creal, b, b);
        let sum = cadd(d, creal, aa, bb);
        let first = d.lemma(creal.sq_nonneg, &[a]);
        let second = d.lemma(creal.sq_nonneg, &[b]);
        let combined = d.lemma(creal.add_le_add, &[zero, aa, zero, bb, first, second]);
        let padded = cadd(d, creal, zero, zero);
        let collapse = d.lemma(creal.add_zero, &[zero]);
        let sum_refl = crefl(d, creal, sum);
        let body = d.lemma(
            creal.le_congr,
            &[padded, zero, sum, sum, collapse, sum_refl, combined],
        );
        let value = d.lam_fv(z_fv, carrier, body);
        let ty = {
            let norm = d.const_app(p.norm_sq, &[z]);
            let claim = d.const_app(creal.le, &[zero, norm]);
            d.pi_fv(z_fv, carrier, claim)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.norm_sq_nonneg,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `normSq_conj` and `normSq_mul`: how the norm interacts with conjugation
/// and multiplication.
///
/// Both are stated over `CReal.Equiv` directly rather than `Complex.Equiv` —
/// `normSq` is `CReal`-valued, so `ring_law_proof`'s `And.intro` of two
/// components does not apply; each is a single call to the underlying
/// [`ring_proof`] on the unfolded `RExpr` forms, exactly the pattern
/// [`declare_norm`]'s `mul_conj` already used for its real component.
fn declare_norm_conjugation(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    // normSq_conj : CReal.Equiv (normSq (conj z)) (normSq z)
    //
    // normSq (conj z) unfolds to a·a + (−b)·(−b); normSq z to a·a + b·b. The
    // ring calculus cancels the double negation, the same move `mul_conj`
    // already relies on.
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let conj_z = d.const_app(p.conj, &[z]);
        let norm_conj = d.const_app(p.norm_sq, &[conj_z]);
        let norm_z = d.const_app(p.norm_sq, &[z]);

        let lhs = RExpr::add(
            RExpr::mul(RExpr::Atom(a), RExpr::Atom(a)),
            RExpr::mul(RExpr::neg(RExpr::Atom(b)), RExpr::neg(RExpr::Atom(b))),
        );
        let rhs = RExpr::add(
            RExpr::mul(RExpr::Atom(a), RExpr::Atom(a)),
            RExpr::mul(RExpr::Atom(b), RExpr::Atom(b)),
        );
        let proof = ring_proof(d, creal, &lhs, &rhs);
        let value = d.lam_fv(z_fv, carrier, proof);
        let ty = {
            let claim = ceq(d, creal, norm_conj, norm_z);
            d.pi_fv(z_fv, carrier, claim)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.norm_sq_conj,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // normSq_mul : CReal.Equiv (normSq (mul z w)) (CReal.mul (normSq z) (normSq w))
    //
    // The Brahmagupta-Fibonacci two-square identity:
    //   (a*c - b*e)^2 + (a*e + b*c)^2 = (a*a + b*b) * (c*c + e*e)
    // Both sides expand to the same four degree-4 monomials
    // {a²c², a²e², b²c², b²e²}; the cross terms ±2·a·c·b·e cancel pairwise,
    // exactly the multiset cancellation the ring calculus already performs.
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let a = re_of(d, p, z);
        let b = im_of(d, p, z);
        let c = re_of(d, p, w);
        let e = im_of(d, p, w);

        let mul_zw = d.const_app(p.mul, &[z, w]);
        let norm_mul = d.const_app(p.norm_sq, &[mul_zw]);
        let norm_z = d.const_app(p.norm_sq, &[z]);
        let norm_w = d.const_app(p.norm_sq, &[w]);
        let norm_prod = cmul(d, creal, norm_z, norm_w);

        // normSq (mul z w) unfolds to (a·c + −(b·e))·(a·c + −(b·e))
        //                            + (a·e + b·c)·(a·e + b·c)
        let ac = RExpr::mul(RExpr::Atom(a), RExpr::Atom(c));
        let be = RExpr::mul(RExpr::Atom(b), RExpr::Atom(e));
        let ae = RExpr::mul(RExpr::Atom(a), RExpr::Atom(e));
        let bc = RExpr::mul(RExpr::Atom(b), RExpr::Atom(c));
        let real_part = RExpr::add(ac, RExpr::neg(be));
        let imag_part = RExpr::add(ae, bc);
        let lhs = RExpr::add(
            RExpr::mul(real_part.clone(), real_part),
            RExpr::mul(imag_part.clone(), imag_part),
        );

        // normSq z * normSq w unfolds to (a·a + b·b) · (c·c + e·e)
        let aa_bb = RExpr::add(
            RExpr::mul(RExpr::Atom(a), RExpr::Atom(a)),
            RExpr::mul(RExpr::Atom(b), RExpr::Atom(b)),
        );
        let cc_ee = RExpr::add(
            RExpr::mul(RExpr::Atom(c), RExpr::Atom(c)),
            RExpr::mul(RExpr::Atom(e), RExpr::Atom(e)),
        );
        let rhs = RExpr::mul(aa_bb, cc_ee);

        let proof = ring_proof(d, creal, &lhs, &rhs);
        let value = {
            let with_w = d.lam_fv(w_fv, carrier, proof);
            d.lam_fv(z_fv, carrier, with_w)
        };
        let ty = {
            let claim = ceq(d, creal, norm_mul, norm_prod);
            let with_w = d.pi_fv(w_fv, carrier, claim);
            d.pi_fv(z_fv, carrier, with_w)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.norm_sq_mul,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Complex.normSq_eq_zero_of_eq_zero`: the **easy** half of
/// `normSq z ~ 0 ↔ z ~ 0`. The converse is
/// [`declare_eq_zero_of_norm_sq_eq_zero`], just below.
fn declare_norm_sq_eq_zero_of_eq_zero(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let hypothesis = zeq(d, p, z, zero_c);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let (re_eq, im_eq) = equiv_halves(d, p, z, zero_c, h);
    // re_eq : Equiv (re z) (re zero_c), defeq to Equiv (re z) CReal.zero.
    // im_eq : Equiv (im z) (im zero_c), defeq to Equiv (im z) CReal.zero.
    let a = re_of(d, p, z);
    let b = im_of(d, p, z);
    let zero = czero(d, creal);

    let aa_eq = d.lemma(creal.mul_congr, &[a, zero, a, zero, re_eq, re_eq]);
    let bb_eq = d.lemma(creal.mul_congr, &[b, zero, b, zero, im_eq, im_eq]);
    let mul_aa = cmul(d, creal, a, a);
    let mul_bb = cmul(d, creal, b, b);
    let mul_zero = cmul(d, creal, zero, zero);
    let aa_bb_eq = d.lemma(
        creal.add_congr,
        &[mul_aa, mul_zero, mul_bb, mul_zero, aa_eq, bb_eq],
    );
    // aa_bb_eq : Equiv (add (a*a) (b*b)) (add (zero*zero) (zero*zero)),
    // and `add (a*a) (b*b)` is defeq to `Complex.normSq z`.
    let collapse = ring_proof(
        d,
        creal,
        &RExpr::add(
            RExpr::mul(RExpr::Zero, RExpr::Zero),
            RExpr::mul(RExpr::Zero, RExpr::Zero),
        ),
        &RExpr::Zero,
    );
    let norm_z = d.const_app(p.norm_sq, &[z]);
    let sum_zz = cadd(d, creal, mul_zero, mul_zero);
    let proof = ctrans(d, creal, norm_z, sum_zz, zero, aa_bb_eq, collapse);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, proof);
        d.lam_fv(z_fv, carrier, with_h)
    };
    let ty = {
        let claim = ceq(d, creal, norm_z, zero);
        let inner = d.arrow(hypothesis, claim);
        d.pi_fv(z_fv, carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.norm_sq_eq_zero_of_eq_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv x CReal.zero`, from `le zero x`, `le zero y` and `Equiv (add x y)
/// zero`.
///
/// The order half of "a zero sum of two nonnegatives forces each addend to
/// zero": `x ≤ x + 0 ≤ x + y ~ 0` (the middle step is `add_le_add` at
/// `le_refl x` and `le_zero_y`, the first is `add_zero` read backwards via
/// `le_congr`), so `x ≤ 0`; combined with the given `0 ≤ x`,
/// `equiv_of_le_le` closes `x ~ 0`. Nothing here is `CReal`-specific beyond
/// the seven lemmas named above, and no such split is itself a named `CReal`
/// lemma — this is the whole of what
/// [`ComplexPrelude::eq_zero_of_norm_sq_eq_zero`] needed that was not already
/// on the shelf.
fn nonneg_sum_zero_left(
    d: &mut IntDev<'_>,
    creal: CRealPrelude,
    x: ExprId,
    y: ExprId,
    le_zero_x: ExprId,
    le_zero_y: ExprId,
    h_sum_zero: ExprId,
) -> ExprId {
    let zero = czero(d, creal);
    let x_plus_zero = cadd(d, creal, x, zero);
    let x_plus_y = cadd(d, creal, x, y);
    let add_zero_x = d.lemma(creal.add_zero, &[x]); // Equiv (add x zero) x
    let le_refl_x = d.lemma(creal.le_refl, &[x]); // le x x
    let step = d.lemma(creal.add_le_add, &[x, x, zero, y, le_refl_x, le_zero_y]);
    // step : le (add x zero) (add x y)
    let refl_xy = crefl(d, creal, x_plus_y);
    let le_x_xy = d.lemma(
        creal.le_congr,
        &[
            x_plus_zero,
            x,
            x_plus_y,
            x_plus_y,
            add_zero_x,
            refl_xy,
            step,
        ],
    );
    // le_x_xy : le x (add x y)
    let le_xy_zero = d.lemma(creal.le_of_equiv, &[x_plus_y, zero, h_sum_zero]);
    let le_x_zero = d.lemma(creal.le_trans, &[x, x_plus_y, zero, le_x_xy, le_xy_zero]);
    d.lemma(creal.equiv_of_le_le, &[x, zero, le_x_zero, le_zero_x])
}

/// `Complex.eq_zero_of_normSq_eq_zero`: the **converse** half of
/// `normSq z ~ 0 ↔ z ~ 0`. See
/// [`ComplexPrelude::eq_zero_of_norm_sq_eq_zero`] for the route.
fn declare_eq_zero_of_norm_sq_eq_zero(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let a = re_of(d, p, z);
    let b = im_of(d, p, z);
    let zero = czero(d, creal);
    let zero_c = d.kernel().const_(p.zero, vec![]);

    let aa = cmul(d, creal, a, a);
    let bb = cmul(d, creal, b, b);
    let norm_z = d.const_app(p.norm_sq, &[z]); // defeq to `add aa bb`

    let hypothesis = ceq(d, creal, norm_z, zero);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    // h : Equiv (normSq z) zero, defeq to Equiv (add aa bb) zero — the same
    // delta-unfolding `declare_norm`'s `normSq_nonneg` and
    // `declare_norm_sq_eq_zero_of_eq_zero` above already rely on.

    let aa_nonneg = d.lemma(creal.sq_nonneg, &[a]);
    let bb_nonneg = d.lemma(creal.sq_nonneg, &[b]);

    let aa_zero = nonneg_sum_zero_left(d, creal, aa, bb, aa_nonneg, bb_nonneg, h);

    // For `bb`, the sum needs to be read in the other order:
    // `add_comm bb aa : Equiv (add bb aa) (add aa bb)`, then `trans` with `h`
    // (defeq: `add aa bb` against `normSq z`) gives `Equiv (add bb aa) zero`.
    let add_bb_aa = cadd(d, creal, bb, aa);
    let add_aa_bb = cadd(d, creal, aa, bb);
    let comm_ba = d.lemma(creal.add_comm, &[bb, aa]); // Equiv (add bb aa) (add aa bb)
    let h_swapped = ctrans(d, creal, add_bb_aa, add_aa_bb, zero, comm_ba, h);
    let bb_zero = nonneg_sum_zero_left(d, creal, bb, aa, bb_nonneg, aa_nonneg, h_swapped);

    let a_zero = d.lemma(creal.eq_zero_of_mul_self_zero, &[a, aa_zero]);
    let b_zero = d.lemma(creal.eq_zero_of_mul_self_zero, &[b, bb_zero]);

    // `re zero_c`/`im zero_c` are defeq to `CReal.zero`, so `a_zero`/`b_zero`
    // (typed `Equiv _ CReal.zero`) close these two components directly.
    let re_zero_c = re_of(d, p, zero_c);
    let im_zero_c = im_of(d, p, zero_c);
    let left_claim = ceq(d, creal, a, re_zero_c);
    let right_claim = ceq(d, creal, b, im_zero_c);
    let body = and_intro(d, p, left_claim, right_claim, a_zero, b_zero);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        d.lam_fv(z_fv, carrier, with_h)
    };
    let ty = {
        let claim = zeq(d, p, z, zero_c);
        let inner = d.arrow(hypothesis, claim);
        d.pi_fv(z_fv, carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.eq_zero_of_norm_sq_eq_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.normSq_eq_zero_iff`: the biconditional, from
/// [`declare_norm_sq_eq_zero_of_eq_zero`] (`mpr`) and
/// [`declare_eq_zero_of_norm_sq_eq_zero`] (`mp`) — a restatement, not a new
/// proof, in the style `pythagoras_distSq` uses in `creal_point.rs`: each
/// half is the existing theorem re-applied as a value.
fn declare_norm_sq_eq_zero_iff(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let logic = creal.rat.int.logic;
    let carrier = complex_ty(d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let zero = czero(d, creal);
    let norm_z = d.const_app(p.norm_sq, &[z]);

    let norm_stmt = ceq(d, creal, norm_z, zero);
    let equiv_stmt = zeq(d, p, z, zero_c);

    // mp : Equiv (normSq z) zero -> Equiv z zero
    let mp_body = d.lemma(p.eq_zero_of_norm_sq_eq_zero, &[z]);
    // mpr : Equiv z zero -> Equiv (normSq z) zero
    let mpr_body = d.lemma(p.norm_sq_eq_zero_of_eq_zero, &[z]);

    let iff_stmt = d.const_app(logic.iff, &[norm_stmt, equiv_stmt]);
    let iff_proof = d.const_app(logic.iff_intro, &[norm_stmt, equiv_stmt, mp_body, mpr_body]);

    let value = d.lam_fv(z_fv, carrier, iff_proof);
    let ty = d.pi_fv(z_fv, carrier, iff_stmt);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.norm_sq_eq_zero_iff,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.normSq_add`: the parallelogram law,
/// `‖z+w‖² + ‖z−w‖² = 2‖z‖² + 2‖w‖²`, with `2·normSq z` written as
/// `normSq z + normSq z` to avoid inventing a convention for multiplying a
/// `CReal` by a `Nat`. A clean unconditional identity — no hypothesis, no
/// case split — decided by the same ring calculus as [`declare_norm_conjugation`].
fn declare_norm_sq_add(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let a = re_of(d, p, z);
    let b = im_of(d, p, z);
    let c = re_of(d, p, w);
    let e = im_of(d, p, w);

    let sum_zw = d.const_app(p.add, &[z, w]);
    let neg_w = d.const_app(p.neg, &[w]);
    let diff_zw = d.const_app(p.add, &[z, neg_w]);
    let norm_sum = d.const_app(p.norm_sq, &[sum_zw]);
    let norm_diff = d.const_app(p.norm_sq, &[diff_zw]);
    let norm_z = d.const_app(p.norm_sq, &[z]);
    let norm_w = d.const_app(p.norm_sq, &[w]);

    let sum_re = RExpr::add(RExpr::Atom(a), RExpr::Atom(c));
    let sum_im = RExpr::add(RExpr::Atom(b), RExpr::Atom(e));
    let diff_re = RExpr::add(RExpr::Atom(a), RExpr::neg(RExpr::Atom(c)));
    let diff_im = RExpr::add(RExpr::Atom(b), RExpr::neg(RExpr::Atom(e)));
    let norm_sum_expr = RExpr::add(
        RExpr::mul(sum_re.clone(), sum_re),
        RExpr::mul(sum_im.clone(), sum_im),
    );
    let norm_diff_expr = RExpr::add(
        RExpr::mul(diff_re.clone(), diff_re),
        RExpr::mul(diff_im.clone(), diff_im),
    );
    let lhs = RExpr::add(norm_sum_expr, norm_diff_expr);

    let aa_bb = RExpr::add(
        RExpr::mul(RExpr::Atom(a), RExpr::Atom(a)),
        RExpr::mul(RExpr::Atom(b), RExpr::Atom(b)),
    );
    let cc_ee = RExpr::add(
        RExpr::mul(RExpr::Atom(c), RExpr::Atom(c)),
        RExpr::mul(RExpr::Atom(e), RExpr::Atom(e)),
    );
    let rhs = RExpr::add(
        RExpr::add(aa_bb.clone(), aa_bb),
        RExpr::add(cc_ee.clone(), cc_ee),
    );

    let proof = ring_proof(d, creal, &lhs, &rhs);
    let lhs_term = cadd(d, creal, norm_sum, norm_diff);
    let norm_z_doubled = cadd(d, creal, norm_z, norm_z);
    let norm_w_doubled = cadd(d, creal, norm_w, norm_w);
    let rhs_term = cadd(d, creal, norm_z_doubled, norm_w_doubled);
    let value = {
        let with_w = d.lam_fv(w_fv, carrier, proof);
        d.lam_fv(z_fv, carrier, with_w)
    };
    let ty = {
        let claim = ceq(d, creal, lhs_term, rhs_term);
        let with_w = d.pi_fv(w_fv, carrier, claim);
        d.pi_fv(z_fv, carrier, with_w)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.norm_sq_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// **ℂ admits no ordered-ring structure**, proved rather than asserted.
///
/// The statement quantifies over the two relations, so it refutes *every*
/// candidate order at once rather than the one this module might have picked.
/// Seven of the `AxReal` package's 13 order laws are enough; `I` is the witness.
fn declare_no_order(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let prop = d.kernel().sort_zero();
    let relation = {
        let inner = d.arrow(carrier, prop);
        d.arrow(carrier, inner)
    };

    let le_fv = d.fresh_fvar();
    let le = d.kernel().fvar(le_fv);
    let lt_fv = d.fresh_fvar();
    let lt = d.kernel().fvar(lt_fv);
    let rel = |d: &mut IntDev<'_>, r: ExprId, a: ExprId, b: ExprId| d.apply(r, &[a, b]);

    // The seven hypotheses, in the `AxReal` package's own shapes.
    let le_refl_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let claim = rel(d, le, x, x);
        d.pi_fv(x_fv, carrier, claim)
    };
    let lt_irrefl_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let claim = rel(d, lt, x, x);
        let negated = d.not(claim);
        d.pi_fv(x_fv, carrier, negated)
    };
    let lt_of_le_of_lt_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let first = rel(d, le, x, y);
        let second = rel(d, lt, y, z);
        let conclusion = rel(d, lt, x, z);
        let after2 = d.arrow(second, conclusion);
        let after1 = d.arrow(first, after2);
        let with_z = d.pi_fv(z_fv, carrier, after1);
        let with_y = d.pi_fv(y_fv, carrier, with_z);
        d.pi_fv(x_fv, carrier, with_y)
    };
    let add_le_add_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let x2_fv = d.fresh_fvar();
        let x2 = d.kernel().fvar(x2_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let y2_fv = d.fresh_fvar();
        let y2 = d.kernel().fvar(y2_fv);
        let first = rel(d, le, x, x2);
        let second = rel(d, le, y, y2);
        let left = d.const_app(p.add, &[x, y]);
        let right = d.const_app(p.add, &[x2, y2]);
        let conclusion = rel(d, le, left, right);
        let after2 = d.arrow(second, conclusion);
        let after1 = d.arrow(first, after2);
        let with_y2 = d.pi_fv(y2_fv, carrier, after1);
        let with_y = d.pi_fv(y_fv, carrier, with_y2);
        let with_x2 = d.pi_fv(x2_fv, carrier, with_y);
        d.pi_fv(x_fv, carrier, with_x2)
    };
    let le_congr_ty = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let first = zeq(d, p, a, b);
        let second = zeq(d, p, c, e);
        let third = rel(d, le, a, c);
        let conclusion = rel(d, le, b, e);
        let after3 = d.arrow(third, conclusion);
        let after2 = d.arrow(second, after3);
        let after1 = d.arrow(first, after2);
        let with_e = d.pi_fv(e_fv, carrier, after1);
        let with_c = d.pi_fv(c_fv, carrier, with_e);
        let with_b = d.pi_fv(b_fv, carrier, with_c);
        d.pi_fv(a_fv, carrier, with_b)
    };
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let sq_nonneg_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let square = d.const_app(p.mul, &[x, x]);
        let claim = rel(d, le, zero, square);
        d.pi_fv(x_fv, carrier, claim)
    };
    let zero_lt_one_ty = rel(d, lt, zero, one);

    // The proof, as the seven hypotheses arrive.
    let h_refl_fv = d.fresh_fvar();
    let h_refl = d.kernel().fvar(h_refl_fv);
    let h_irrefl_fv = d.fresh_fvar();
    let h_irrefl = d.kernel().fvar(h_irrefl_fv);
    let h_mixed_fv = d.fresh_fvar();
    let h_mixed = d.kernel().fvar(h_mixed_fv);
    let h_add_fv = d.fresh_fvar();
    let h_add = d.kernel().fvar(h_add_fv);
    let h_congr_fv = d.fresh_fvar();
    let h_congr = d.kernel().fvar(h_congr_fv);
    let h_sq_fv = d.fresh_fvar();
    let h_sq = d.kernel().fvar(h_sq_fv);
    let h_one_fv = d.fresh_fvar();
    let h_one = d.kernel().fvar(h_one_fv);

    let imaginary = d.kernel().const_(p.i, vec![]);
    let square = d.const_app(p.mul, &[imaginary, imaginary]);
    let negated_one = d.const_app(p.neg, &[one]);

    // 0 ≤ I·I, and I·I ~ −1, so 0 ≤ −1.
    let square_nonneg = d.apply(h_sq, &[imaginary]);
    let zero_refl = d.lemma(p.equiv_refl, &[zero]);
    let i_sq = d.kernel().const_(p.i_sq, vec![]);
    let neg_one_nonneg = d.apply(
        h_congr,
        &[
            zero,
            zero,
            square,
            negated_one,
            zero_refl,
            i_sq,
            square_nonneg,
        ],
    );

    // 1 + 0 ≤ 1 + (−1), i.e. 1 ≤ 0.
    let one_refl = d.apply(h_refl, &[one]);
    let padded = d.apply(
        h_add,
        &[one, one, zero, negated_one, one_refl, neg_one_nonneg],
    );
    let left_sum = d.const_app(p.add, &[one, zero]);
    let right_sum = d.const_app(p.add, &[one, negated_one]);
    let trim_left = d.lemma(p.add_zero, &[one]);
    let trim_right = d.lemma(p.add_neg, &[one]);
    let one_le_zero = d.apply(
        h_congr,
        &[
            left_sum, one, right_sum, zero, trim_left, trim_right, padded,
        ],
    );

    // 1 ≤ 0 and 0 < 1 give 1 < 1, which `lt_irrefl` refuses.
    let one_lt_one = d.apply(h_mixed, &[one, zero, one, one_le_zero, h_one]);
    let body = d.apply(h_irrefl, &[one, one_lt_one]);

    let value = {
        let mut acc = body;
        acc = d.lam_fv(h_one_fv, zero_lt_one_ty, acc);
        acc = d.lam_fv(h_sq_fv, sq_nonneg_ty, acc);
        acc = d.lam_fv(h_congr_fv, le_congr_ty, acc);
        acc = d.lam_fv(h_add_fv, add_le_add_ty, acc);
        acc = d.lam_fv(h_mixed_fv, lt_of_le_of_lt_ty, acc);
        acc = d.lam_fv(h_irrefl_fv, lt_irrefl_ty, acc);
        acc = d.lam_fv(h_refl_fv, le_refl_ty, acc);
        acc = d.lam_fv(lt_fv, relation, acc);
        d.lam_fv(le_fv, relation, acc)
    };
    let ty = {
        let false_ty = d.false_ty();
        let mut acc = false_ty;
        acc = d.arrow(zero_lt_one_ty, acc);
        acc = d.arrow(sq_nonneg_ty, acc);
        acc = d.arrow(le_congr_ty, acc);
        acc = d.arrow(add_le_add_ty, acc);
        acc = d.arrow(lt_of_le_of_lt_ty, acc);
        acc = d.arrow(lt_irrefl_ty, acc);
        acc = d.arrow(le_refl_ty, acc);
        acc = d.pi_fv(lt_fv, relation, acc);
        d.pi_fv(le_fv, relation, acc)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.no_compatible_order,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the multiplicative inverse, and ℂ as a field ---------------------------
//
// `CReal.inv`'s actual signature, read out of `creal/inverse.rs`:
//
//   CReal.inv : (x : CReal) → (k : Nat) → CReal.PosBound x k → CReal
//
// with `CReal.PosBound x k := CReal.le (CReal.ofRat (Rat.natDivSucc 1 k)) x` —
// an explicit witnessed lower bound, not apartness from zero. `Complex.inv`
// below takes the same shape verbatim, instantiated at `x := normSq z`: ℂ
// carries no order of its own to phrase positivity in, so the separating
// quantity has to be the (`CReal`-valued, already-ordered) norm.

/// `Complex.inv z k h := mk (re z · CReal.inv (normSq z) k h)
/// (−(im z · CReal.inv (normSq z) k h))`.
///
/// Mirrors `CReal.inv`'s own convention rather than inventing a second one:
/// the modulus `k` and the witness `h : CReal.PosBound (normSq z) k` are data
/// the caller supplies. `h` is consumed only inside `CReal.inv`'s own
/// `Prop`-valued obligation, never branched on, so this never eliminates a
/// disjunction into `Type` — the same reason `CReal.inv` itself is definable.
fn declare_inv(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm = d.const_app(p.norm_sq, &[z]);
    let hypothesis = d.const_app(creal.pos_bound, &[norm, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let a = re_of(d, p, z);
    let b = im_of(d, p, z);
    let inv_norm = d.const_app(creal.inv, &[norm, k, h]);
    let real_part = cmul(d, creal, a, inv_norm);
    let b_inv_norm = cmul(d, creal, b, inv_norm);
    let imag_part = cneg(d, creal, b_inv_norm);

    let constructor = d.kernel().const_(p.mk, vec![]);
    let body = d.apply(constructor, &[real_part, imag_part]);
    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(z_fv, carrier, with_k)
    };
    let ty = {
        let inner = d.arrow(hypothesis, carrier);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(z_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.inv,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 6),
    })
}

/// `Complex.mul_inv_cancel : ∀ z k (h : CReal.PosBound (normSq z) k),
/// Equiv (mul z (inv z k h)) one` — **the field law**, and the theorem that
/// makes ℂ more than a ring with a division-shaped function bolted on.
///
/// The imaginary part of `z · z⁻¹` cancels as a **pure ring identity** —
/// `a·(−(b·u)) + b·(a·u)` is two opposite monomials — with no external fact
/// needed at all. The real part rewrites, by the same ring calculus, to
/// `(re z · re z + im z · im z) · CReal.inv (normSq z) k h`, and that sum
/// **is** `normSq z` by one delta step of `normSq`'s own definition — so
/// `CReal.mul_inv_cancel (normSq z) k h` closes it directly: no bridging
/// lemma is needed, only the kernel's definitional unfolding lining the two
/// shapes up.
fn declare_complex_mul_inv_cancel(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm = d.const_app(p.norm_sq, &[z]);
    let hypothesis = d.const_app(creal.pos_bound, &[norm, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let a = re_of(d, p, z);
    let b = im_of(d, p, z);
    let inv_norm = d.const_app(creal.inv, &[norm, k, h]);

    // The real/imaginary parts of `inv z k h`, in the ring calculus's own
    // language -- exactly what `re (inv z k h)` / `im (inv z k h)` reduce to
    // by one delta step on `Complex.inv` plus one iota step over its `mk`.
    let c_expr = RExpr::mul(RExpr::Atom(a), RExpr::Atom(inv_norm));
    let e_expr = RExpr::neg(RExpr::mul(RExpr::Atom(b), RExpr::Atom(inv_norm)));

    // `mul z (inv z k h)`'s two components, per `Complex.mul`'s own
    // definition: real = a·c + −(b·e), imag = a·e + b·c.
    let real_expr = RExpr::add(
        RExpr::mul(RExpr::Atom(a), c_expr.clone()),
        RExpr::neg(RExpr::mul(RExpr::Atom(b), e_expr.clone())),
    );
    let imag_expr = RExpr::add(
        RExpr::mul(RExpr::Atom(a), e_expr),
        RExpr::mul(RExpr::Atom(b), c_expr),
    );

    // Imaginary part: `a·(−(b·u)) + b·(a·u) ~ 0`, a pure ring identity.
    let imag_proof = ring_proof(d, creal, &imag_expr, &RExpr::Zero);
    let imag_actual = ring::render(d, creal, &imag_expr);
    let zero = czero(d, creal);
    let imag_claim = ceq(d, creal, imag_actual, zero);

    // Real part: rewrite to `(a·a + b·b) · u`, definitionally `normSq z · u`,
    // then close with `CReal.mul_inv_cancel`.
    let expanded = RExpr::mul(
        RExpr::add(
            RExpr::mul(RExpr::Atom(a), RExpr::Atom(a)),
            RExpr::mul(RExpr::Atom(b), RExpr::Atom(b)),
        ),
        RExpr::Atom(inv_norm),
    );
    let rearrange = ring_proof(d, creal, &real_expr, &expanded);
    let real_actual = ring::render(d, creal, &real_expr);
    let expanded_term = ring::render(d, creal, &expanded);
    let one_real = cone(d, creal);
    let cancel = d.lemma(creal.mul_inv_cancel, &[norm, k, h]);
    let real_proof = ctrans(
        d,
        creal,
        real_actual,
        expanded_term,
        one_real,
        rearrange,
        cancel,
    );
    let real_claim = ceq(d, creal, real_actual, one_real);

    let body = and_intro(d, p, real_claim, imag_claim, real_proof, imag_proof);

    let inv_term = d.const_app(p.inv, &[z, k, h]);
    let product = d.const_app(p.mul, &[z, inv_term]);
    let one = d.kernel().const_(p.one, vec![]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(z_fv, carrier, with_k)
    };
    let ty = {
        let conclusion = zeq(d, p, product, one);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(z_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_inv_cancel,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.inv_congr : ∀ z z' k k' (h : PosBound (normSq z) k)
/// (h' : PosBound (normSq z') k'), Equiv z z' →
/// Equiv (inv z k h) (inv z' k' h')`.
///
/// **Without this `Complex.inv` is a function on representatives, not on
/// ℂ.** The statement quantifies over `k` and `k'` independently, exactly as
/// `CReal.inv_congr` does, since two callers holding different separating
/// moduli for `Equiv`-related `z`/`z'` build different sequences underneath.
///
/// The proof is not a fresh estimate: `normSq z ~ normSq z'` follows from the
/// hypothesis' two halves by the ring congruences alone (`mul_congr` twice,
/// `add_congr` once), and `CReal.inv_congr` — built for exactly this
/// independent-moduli shape — turns that into
/// `CReal.inv (normSq z) k h ~ CReal.inv (normSq z') k' h'` directly. The two
/// `Complex.Equiv` halves are `mul_congr`/`neg_congr` on that single fact.
fn declare_complex_inv_congr(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let z2_fv = d.fresh_fvar();
    let z2 = d.kernel().fvar(z2_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);

    let norm = d.const_app(p.norm_sq, &[z]);
    let norm2 = d.const_app(p.norm_sq, &[z2]);
    let hypothesis = d.const_app(creal.pos_bound, &[norm, k]);
    let hypothesis2 = d.const_app(creal.pos_bound, &[norm2, k2]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let related = zeq(d, p, z, z2);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);

    let a = re_of(d, p, z);
    let b = im_of(d, p, z);
    let a2 = re_of(d, p, z2);
    let b2 = im_of(d, p, z2);
    let (ha, hb) = equiv_halves(d, p, z, z2, he);

    // `normSq z ~ normSq z'`, via the ring congruences.
    let maa = d.lemma(creal.mul_congr, &[a, a2, a, a2, ha, ha]);
    let mbb = d.lemma(creal.mul_congr, &[b, b2, b, b2, hb, hb]);
    let aa = cmul(d, creal, a, a);
    let aa2 = cmul(d, creal, a2, a2);
    let bb = cmul(d, creal, b, b);
    let bb2 = cmul(d, creal, b2, b2);
    let hn_expanded = d.lemma(creal.add_congr, &[aa, aa2, bb, bb2, maa, mbb]);

    // `CReal.inv (normSq z) k h ~ CReal.inv (normSq z') k' h'`.
    let inv_norm = d.const_app(creal.inv, &[norm, k, h]);
    let inv_norm2 = d.const_app(creal.inv, &[norm2, k2, h2]);
    let hi = d.lemma(creal.inv_congr, &[norm, norm2, k, k2, h, h2, hn_expanded]);

    // real: a·u ~ a'·u'; imag: −(b·u) ~ −(b'·u').
    let real_proof = d.lemma(creal.mul_congr, &[a, a2, inv_norm, inv_norm2, ha, hi]);
    let mbi = d.lemma(creal.mul_congr, &[b, b2, inv_norm, inv_norm2, hb, hi]);
    let bu = cmul(d, creal, b, inv_norm);
    let bu2 = cmul(d, creal, b2, inv_norm2);
    let imag_proof = d.lemma(creal.neg_congr, &[bu, bu2, mbi]);

    let au = cmul(d, creal, a, inv_norm);
    let au2 = cmul(d, creal, a2, inv_norm2);
    let real_claim = ceq(d, creal, au, au2);
    let nbu = cneg(d, creal, bu);
    let nbu2 = cneg(d, creal, bu2);
    let imag_claim = ceq(d, creal, nbu, nbu2);
    let body = and_intro(d, p, real_claim, imag_claim, real_proof, imag_proof);

    let inv_z = d.const_app(p.inv, &[z, k, h]);
    let inv_z2 = d.const_app(p.inv, &[z2, k2, h2]);

    let value = {
        let with_he = d.lam_fv(he_fv, related, body);
        let with_h2 = d.lam_fv(h2_fv, hypothesis2, with_he);
        let with_h = d.lam_fv(h_fv, hypothesis, with_h2);
        let with_k2 = d.lam_fv(k2_fv, nat, with_h);
        let with_k = d.lam_fv(k_fv, nat, with_k2);
        let with_z2 = d.lam_fv(z2_fv, carrier, with_k);
        d.lam_fv(z_fv, carrier, with_z2)
    };
    let ty = {
        let conclusion = zeq(d, p, inv_z, inv_z2);
        let after_he = d.arrow(related, conclusion);
        let with_h2 = d.pi_fv(h2_fv, hypothesis2, after_he);
        let with_h = d.pi_fv(h_fv, hypothesis, with_h2);
        let with_k2 = d.pi_fv(k2_fv, nat, with_h);
        let with_k = d.pi_fv(k_fv, nat, with_k2);
        let with_z2 = d.pi_fv(z2_fv, carrier, with_k);
        d.pi_fv(z_fv, carrier, with_z2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.inv_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.div z w k h := mul z (inv w k h)`.
///
/// Guarded by the **divisor's** norm: `h : CReal.PosBound (normSq w) k`, not
/// the dividend's — dividing `z` by `w` needs `w` bounded away from zero.
fn declare_div(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm_w = d.const_app(p.norm_sq, &[w]);
    let hypothesis = d.const_app(creal.pos_bound, &[norm_w, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let inv_w = d.const_app(p.inv, &[w, k, h]);
    let value_body = d.const_app(p.mul, &[z, inv_w]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, value_body);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_w = d.lam_fv(w_fv, carrier, with_k);
        d.lam_fv(z_fv, carrier, with_w)
    };
    let ty = {
        let inner = d.arrow(hypothesis, carrier);
        let with_k = d.pi_fv(k_fv, nat, inner);
        let with_w = d.pi_fv(w_fv, carrier, with_k);
        d.pi_fv(z_fv, carrier, with_w)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.div,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 7),
    })
}

/// `Complex.div_self : ∀ z k (h : PosBound (normSq z) k),
/// Equiv (div z z k h) one` — `z / z ~ 1`.
///
/// **One sanity identity, and nothing more elaborate**: `div z z k h` unfolds
/// by a single delta step (substituting `w := z`) to exactly
/// `mul z (inv z k h)`, so [`ComplexPrelude::mul_inv_cancel`] applied at `z`
/// itself already has the type this theorem states.
fn declare_div_self(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm = d.const_app(p.norm_sq, &[z]);
    let hypothesis = d.const_app(p.creal.pos_bound, &[norm, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let cancel = d.lemma(p.mul_inv_cancel, &[z, k, h]);

    let div_zz = d.const_app(p.div, &[z, z, k, h]);
    let one = d.kernel().const_(p.one, vec![]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, cancel);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(z_fv, carrier, with_k)
    };
    let ty = {
        let conclusion = zeq(d, p, div_zz, one);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(z_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.div_self,
        uparams: vec![],
        ty,
        value,
    })
}

// --- apartness, and the constructive shape of "no zero divisors" -----------
//
// ℂ has no order ([`declare_no_order`]), so `Complex.Apart` cannot mirror
// `CReal.Apart`'s *shape* (`lt x y ∨ lt y x`): there is no `lt` on `Complex`
// to disjoin. It mirrors `CReal.Apart`'s *role* — a `Prop` strictly stronger
// than `Not Equiv` — through the one order ℂ's components still have: `normSq
// (z − w)` is always `CReal.le`-nonneg, so its **strict** positivity is
// exactly the separation `Apart` needs, ported through `CReal.lt` directly.

/// `CReal.Equiv (normSq v) (normSq (add v (neg Complex.zero)))`.
///
/// The bridging identity every `Apart _ Complex.zero` proof goes through:
/// `Apart v zero` unfolds to positivity of `normSq (add v (neg zero))`, a
/// *different* term from `normSq v` (though ring-equal — `add v (neg zero)`
/// needs a rearrangement, not defeq, since `CReal.add`/`neg` do not compute
/// syntactically on an opaque variable). Both sides are built already
/// unfolded one delta step past `normSq`/`add`/`neg`/`Complex.zero`, exactly
/// the pattern [`declare_norm_conjugation`]'s `normSq_mul` uses, so the ring
/// calculus's output type-checks against the folded target by the kernel's
/// own defeq.
fn normsq_shift_zero_proof(d: &mut IntDev<'_>, p: ComplexPrelude, v: ExprId) -> ExprId {
    let creal = p.creal;
    let a = re_of(d, p, v);
    let b = im_of(d, p, v);
    let lhs = RExpr::add(
        RExpr::mul(RExpr::Atom(a), RExpr::Atom(a)),
        RExpr::mul(RExpr::Atom(b), RExpr::Atom(b)),
    );
    let rhs = RExpr::add(
        RExpr::mul(
            RExpr::add(RExpr::Atom(a), RExpr::neg(RExpr::Zero)),
            RExpr::add(RExpr::Atom(a), RExpr::neg(RExpr::Zero)),
        ),
        RExpr::mul(
            RExpr::add(RExpr::Atom(b), RExpr::neg(RExpr::Zero)),
            RExpr::add(RExpr::Atom(b), RExpr::neg(RExpr::Zero)),
        ),
    );
    ring_proof(d, creal, &lhs, &rhs)
}

/// `CReal.Equiv (normSq (add w (neg z))) (normSq (add z (neg w)))`.
///
/// `(c−a)² + (e−b)²` and `(a−c)² + (b−e)²` are the *same* multiset of degree-2
/// monomials — the ring calculus's atom-sorted normal form does not
/// distinguish `a·c` from `c·a`, so the two expand to identical canonical
/// forms with no `CReal.neg_mul_neg`-style side lemma needed.
fn normsq_swap_proof(d: &mut IntDev<'_>, p: ComplexPrelude, z: ExprId, w: ExprId) -> ExprId {
    let creal = p.creal;
    let a = re_of(d, p, z);
    let b = im_of(d, p, z);
    let c = re_of(d, p, w);
    let e = im_of(d, p, w);
    let lhs = RExpr::add(
        RExpr::mul(
            RExpr::add(RExpr::Atom(c), RExpr::neg(RExpr::Atom(a))),
            RExpr::add(RExpr::Atom(c), RExpr::neg(RExpr::Atom(a))),
        ),
        RExpr::mul(
            RExpr::add(RExpr::Atom(e), RExpr::neg(RExpr::Atom(b))),
            RExpr::add(RExpr::Atom(e), RExpr::neg(RExpr::Atom(b))),
        ),
    );
    let rhs = RExpr::add(
        RExpr::mul(
            RExpr::add(RExpr::Atom(a), RExpr::neg(RExpr::Atom(c))),
            RExpr::add(RExpr::Atom(a), RExpr::neg(RExpr::Atom(c))),
        ),
        RExpr::mul(
            RExpr::add(RExpr::Atom(b), RExpr::neg(RExpr::Atom(e))),
            RExpr::add(RExpr::Atom(b), RExpr::neg(RExpr::Atom(e))),
        ),
    );
    ring_proof(d, creal, &lhs, &rhs)
}

/// `Complex.Apart z w := CReal.lt CReal.zero (normSq (add z (neg w)))`.
fn declare_apart(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let prop = d.kernel().sort_zero();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);

    let neg_w = d.const_app(p.neg, &[w]);
    let diff = d.const_app(p.add, &[z, neg_w]);
    let norm_diff = d.const_app(p.norm_sq, &[diff]);
    let zero = czero(d, creal);
    let body = d.const_app(creal.lt, &[zero, norm_diff]);

    let value = {
        let with_w = d.lam_fv(w_fv, carrier, body);
        d.lam_fv(z_fv, carrier, with_w)
    };
    let ty = {
        let inner = d.arrow(carrier, prop);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.apart,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 8),
    })
}

/// `Complex.apart_irrefl : ∀ z, Not (Apart z z)`.
fn declare_apart_irrefl(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let a = re_of(d, p, z);
    let b = im_of(d, p, z);
    let lhs = RExpr::add(
        RExpr::mul(
            RExpr::add(RExpr::Atom(a), RExpr::neg(RExpr::Atom(a))),
            RExpr::add(RExpr::Atom(a), RExpr::neg(RExpr::Atom(a))),
        ),
        RExpr::mul(
            RExpr::add(RExpr::Atom(b), RExpr::neg(RExpr::Atom(b))),
            RExpr::add(RExpr::Atom(b), RExpr::neg(RExpr::Atom(b))),
        ),
    );
    let zero_eq_proof = ring_proof(d, creal, &lhs, &RExpr::Zero);

    let neg_z = d.const_app(p.neg, &[z]);
    let diff = d.const_app(p.add, &[z, neg_z]);
    let norm_diff = d.const_app(p.norm_sq, &[diff]);
    let zero = czero(d, creal);
    let zero_refl = crefl(d, creal, zero);

    let apart_zz = d.const_app(p.apart, &[z, z]);
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let contradiction = d.lemma(
        creal.lt_congr,
        &[zero, zero, norm_diff, zero, zero_refl, zero_eq_proof, hyp],
    );
    let irrefl_zero = d.lemma(creal.lt_irrefl, &[zero]);
    let absurd = d.apply(irrefl_zero, &[contradiction]);

    let value = {
        let with_hyp = d.lam_fv(hyp_fv, apart_zz, absurd);
        d.lam_fv(z_fv, carrier, with_hyp)
    };
    let ty = {
        let not_apart = d.not(apart_zz);
        d.pi_fv(z_fv, carrier, not_apart)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.apart_irrefl,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.apart_symm : ∀ z w, Apart z w → Apart w z`.
fn declare_apart_symm(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);

    let apart_zw = d.const_app(p.apart, &[z, w]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = czero(d, creal);
    let zero_refl = crefl(d, creal, zero);

    let neg_w = d.const_app(p.neg, &[w]);
    let diff_zw = d.const_app(p.add, &[z, neg_w]);
    let norm_zw = d.const_app(p.norm_sq, &[diff_zw]);

    let neg_z = d.const_app(p.neg, &[z]);
    let diff_wz = d.const_app(p.add, &[w, neg_z]);
    let norm_wz = d.const_app(p.norm_sq, &[diff_wz]);

    let swap = normsq_swap_proof(d, p, z, w);
    let swap_symm = csymm(d, creal, norm_wz, norm_zw, swap);

    let conclusion = d.lemma(
        creal.lt_congr,
        &[zero, zero, norm_zw, norm_wz, zero_refl, swap_symm, h],
    );

    let apart_wz = d.const_app(p.apart, &[w, z]);

    let value = {
        let with_h = d.lam_fv(h_fv, apart_zw, conclusion);
        let with_w = d.lam_fv(w_fv, carrier, with_h);
        d.lam_fv(z_fv, carrier, with_w)
    };
    let ty = {
        let inner = d.arrow(apart_zw, apart_wz);
        let with_w = d.pi_fv(w_fv, carrier, inner);
        d.pi_fv(z_fv, carrier, with_w)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.apart_symm,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.apart_of_normSq_pos : ∀ z, CReal.lt CReal.zero (normSq z) →
/// Apart z Complex.zero`.
fn declare_apart_of_normsq_pos(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let norm_z = d.const_app(p.norm_sq, &[z]);
    let zero = czero(d, creal);
    let hyp_ty = d.const_app(creal.lt, &[zero, norm_z]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let shift = normsq_shift_zero_proof(d, p, z);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let neg_zero_c = d.const_app(p.neg, &[zero_c]);
    let diff_z0 = d.const_app(p.add, &[z, neg_zero_c]);
    let norm_z0 = d.const_app(p.norm_sq, &[diff_z0]);

    let zero_refl = crefl(d, creal, zero);
    let conclusion = d.lemma(
        creal.lt_congr,
        &[zero, zero, norm_z, norm_z0, zero_refl, shift, h],
    );

    let apart_z_zero = d.const_app(p.apart, &[z, zero_c]);

    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, conclusion);
        d.lam_fv(z_fv, carrier, with_h)
    };
    let ty = {
        let inner = d.arrow(hyp_ty, apart_z_zero);
        d.pi_fv(z_fv, carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.apart_of_normsq_pos,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.mul_apart_zero : ∀ z w, Apart z zero → Apart w zero →
/// Apart (mul z w) zero` — the constructive shape of "ℂ has no zero
/// divisors".
fn declare_mul_apart_zero(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let apart_z0 = d.const_app(p.apart, &[z, zero_c]);
    let apart_w0 = d.const_app(p.apart, &[w, zero_c]);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let zero = czero(d, creal);
    let zero_refl = crefl(d, creal, zero);
    let neg_zero_c = d.const_app(p.neg, &[zero_c]);

    // pos_z : CReal.lt zero (normSq z), from h1 : Apart z zero.
    let diff_z0 = d.const_app(p.add, &[z, neg_zero_c]);
    let norm_z0 = d.const_app(p.norm_sq, &[diff_z0]);
    let norm_z = d.const_app(p.norm_sq, &[z]);
    let shift_z = normsq_shift_zero_proof(d, p, z);
    let shift_z_symm = csymm(d, creal, norm_z, norm_z0, shift_z);
    let pos_z = d.lemma(
        creal.lt_congr,
        &[zero, zero, norm_z0, norm_z, zero_refl, shift_z_symm, h1],
    );

    // pos_w : CReal.lt zero (normSq w), from h2 : Apart w zero.
    let diff_w0 = d.const_app(p.add, &[w, neg_zero_c]);
    let norm_w0 = d.const_app(p.norm_sq, &[diff_w0]);
    let norm_w = d.const_app(p.norm_sq, &[w]);
    let shift_w = normsq_shift_zero_proof(d, p, w);
    let shift_w_symm = csymm(d, creal, norm_w, norm_w0, shift_w);
    let pos_w = d.lemma(
        creal.lt_congr,
        &[zero, zero, norm_w0, norm_w, zero_refl, shift_w_symm, h2],
    );

    // prod_pos : CReal.lt zero (CReal.mul (normSq z) (normSq w)).
    let prod_pos = d.lemma(creal.mul_pos, &[norm_z, norm_w, pos_z, pos_w]);

    // pos_mul : CReal.lt zero (normSq (mul z w)), via normSq_mul.
    let mul_zw = d.const_app(p.mul, &[z, w]);
    let norm_mul = d.const_app(p.norm_sq, &[mul_zw]);
    let norm_prod = cmul(d, creal, norm_z, norm_w);
    let norm_sq_mul_proof = d.lemma(p.norm_sq_mul, &[z, w]);
    let norm_sq_mul_symm = csymm(d, creal, norm_mul, norm_prod, norm_sq_mul_proof);
    let pos_mul = d.lemma(
        creal.lt_congr,
        &[
            zero,
            zero,
            norm_prod,
            norm_mul,
            zero_refl,
            norm_sq_mul_symm,
            prod_pos,
        ],
    );

    // final : Apart (mul z w) zero.
    let shift_mul = normsq_shift_zero_proof(d, p, mul_zw);
    let diff_mul0 = d.const_app(p.add, &[mul_zw, neg_zero_c]);
    let norm_mul0 = d.const_app(p.norm_sq, &[diff_mul0]);
    let final_proof = d.lemma(
        creal.lt_congr,
        &[
            zero, zero, norm_mul, norm_mul0, zero_refl, shift_mul, pos_mul,
        ],
    );

    let apart_mul0 = d.const_app(p.apart, &[mul_zw, zero_c]);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, apart_w0, final_proof);
        let with_h1 = d.lam_fv(h1_fv, apart_z0, with_h2);
        let with_w = d.lam_fv(w_fv, carrier, with_h1);
        d.lam_fv(z_fv, carrier, with_w)
    };
    let ty = {
        let after2 = d.arrow(apart_w0, apart_mul0);
        let after1 = d.arrow(apart_z0, after2);
        let with_w = d.pi_fv(w_fv, carrier, after1);
        d.pi_fv(z_fv, carrier, with_w)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_apart_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Not (Complex.Equiv v Complex.zero)`, given `apart_v : Apart v
/// Complex.zero`.
///
/// The bridge [`declare_mul_eq_zero_not_both_apart_zero`] needs and no other
/// caller does, so it stays a private proof-term builder rather than a named
/// declaration — exactly [`double_zero_imp_zero`]'s convention.
fn not_equiv_zero_of_apart_zero(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    v: ExprId,
    apart_v: ExprId,
) -> ExprId {
    let creal = p.creal;
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let hyp_ty = zeq(d, p, v, zero_c);

    // From `v ~ zero`: `normSq v ~ CReal.zero` (the easy half already proved).
    let normsq_zero = d.lemma(p.norm_sq_eq_zero_of_eq_zero, &[v, h]);

    let shift = normsq_shift_zero_proof(d, p, v);
    let norm_v = d.const_app(p.norm_sq, &[v]);
    let neg_zero_c = d.const_app(p.neg, &[zero_c]);
    let diff_v0 = d.const_app(p.add, &[v, neg_zero_c]);
    let norm_v0 = d.const_app(p.norm_sq, &[diff_v0]);
    let zero_r = czero(d, creal);

    let shift_symm = csymm(d, creal, norm_v, norm_v0, shift);
    let combined = ctrans(d, creal, norm_v0, norm_v, zero_r, shift_symm, normsq_zero);

    let zero_refl = crefl(d, creal, zero_r);
    let contradiction = d.lemma(
        creal.lt_congr,
        &[
            zero_r, zero_r, norm_v0, zero_r, zero_refl, combined, apart_v,
        ],
    );
    let irrefl = d.lemma(creal.lt_irrefl, &[zero_r]);
    let absurd = d.apply(irrefl, &[contradiction]);

    d.lam_fv(h_fv, hyp_ty, absurd)
}

/// `Complex.mul_eq_zero_not_both_apart_zero : ∀ z w, Equiv (mul z w) zero →
/// Not (And (Apart z zero) (Apart w zero))`.
///
/// **The intuitionistically valid half of "no zero divisors."**
/// `(A → ¬B) ↔ (B → ¬A)` holds without excluded middle (both sides are `A ∧ B
/// → False`, curried), so this is [`declare_mul_apart_zero`] transposed
/// against [`ComplexPrelude::norm_sq_eq_zero_of_eq_zero`] — no `Classical.em`,
/// no `Decidable` instance, nowhere. **Not attempted**: the full disjunctive
/// `mul z w ~ 0 → z ~ 0 ∨ w ~ 0` — `CReal`'s order is not decidable, so that
/// disjunction is not known to be extractable from these hypotheses, and this
/// contrapositive-shaped statement is the constructively available substitute.
fn declare_mul_eq_zero_not_both_apart_zero(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);

    let mul_zw = d.const_app(p.mul, &[z, w]);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let eq_hyp_ty = zeq(d, p, mul_zw, zero_c);
    let eq_fv = d.fresh_fvar();
    let eq_h = d.kernel().fvar(eq_fv);

    let apart_z0 = d.const_app(p.apart, &[z, zero_c]);
    let apart_w0 = d.const_app(p.apart, &[w, zero_c]);
    let and_ty = d.and(apart_z0, apart_w0);
    let and_fv = d.fresh_fvar();
    let and_h = d.kernel().fvar(and_fv);

    let a1 = d.and_left(apart_z0, apart_w0, and_h);
    let a2 = d.and_right(apart_z0, apart_w0, and_h);

    let apart_mul = d.lemma(p.mul_apart_zero, &[z, w, a1, a2]);
    let contra = not_equiv_zero_of_apart_zero(d, p, mul_zw, apart_mul);
    let absurd = d.apply(contra, &[eq_h]);

    let value = {
        let with_and = d.lam_fv(and_fv, and_ty, absurd);
        let with_eq = d.lam_fv(eq_fv, eq_hyp_ty, with_and);
        let with_w = d.lam_fv(w_fv, carrier, with_eq);
        d.lam_fv(z_fv, carrier, with_w)
    };
    let ty = {
        let not_and = d.not(and_ty);
        let inner = d.arrow(eq_hyp_ty, not_and);
        let with_w = d.pi_fv(w_fv, carrier, inner);
        d.pi_fv(z_fv, carrier, with_w)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_eq_zero_not_both_apart_zero,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the other side of the field law, `PosBound` transport, and powers -----

/// `Eq.{1} Complex a b`.
///
/// `Complex` lives at the same universe `Int` does (`declare_carrier`'s
/// `level_one`), so this is exactly [`IntDev`]'s own `ieq` with the carrier
/// swapped — built by hand here rather than reused because `ieq` is hardwired
/// to `Int`.
fn complex_eq(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.creal.rat.int.logic;
    let eq = d.kernel().const_(logic.eq, vec![one]);
    let carrier = complex_ty(d, p);
    d.apply(eq, &[carrier, a, b])
}

/// `Eq.refl.{1} Complex a`.
fn complex_eq_refl(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.creal.rat.int.logic;
    let refl = d.kernel().const_(logic.eq_refl, vec![one]);
    let carrier = complex_ty(d, p);
    d.apply(refl, &[carrier, a])
}

/// `Complex.inv_mul_cancel : ∀ z k (h : CReal.PosBound (normSq z) k),
/// Equiv (mul (inv z k h) z) one`.
///
/// The other side of [`ComplexPrelude::mul_inv_cancel`] — `mul_comm` at
/// `(inv z k h, z)` turns `mul (inv z k h) z` into `mul z (inv z k h)`, and
/// `mul_inv_cancel` itself closes from there. No fresh estimate.
fn declare_complex_inv_mul_cancel(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm = d.const_app(p.norm_sq, &[z]);
    let hypothesis = d.const_app(creal.pos_bound, &[norm, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let inv_term = d.const_app(p.inv, &[z, k, h]);
    let one = d.kernel().const_(p.one, vec![]);

    let inv_z_mul = d.const_app(p.mul, &[inv_term, z]);
    let z_inv_mul = d.const_app(p.mul, &[z, inv_term]);
    let comm = d.lemma(p.mul_comm, &[inv_term, z]); // Equiv (mul inv_term z) (mul z inv_term)
    let cancel = d.lemma(p.mul_inv_cancel, &[z, k, h]); // Equiv (mul z inv_term) one
    let proof = d.lemma(p.equiv_trans, &[inv_z_mul, z_inv_mul, one, comm, cancel]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, proof);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(z_fv, carrier, with_k)
    };
    let ty = {
        let conclusion = zeq(d, p, inv_z_mul, one);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(z_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.inv_mul_cancel,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.pos_bound_conj : ∀ z k, CReal.PosBound (normSq z) k →
/// CReal.PosBound (normSq (conj z)) k`.
///
/// `CReal.PosBound x k` unfolds to `CReal.le (CReal.ofRat (Rat.natDivSucc 1
/// k)) x` — a bound depending on `k` alone — so [`ComplexPrelude::norm_sq_conj`]
/// transports `h` across the *same* `k` by `CReal.le_congr`, with the bound
/// term held fixed by reflexivity on both sides. No existential
/// re-derivation through `CReal.pos_bound_of_lt`, which would hand back an
/// unrelated modulus instead of the caller's own `k`.
fn declare_pos_bound_conj(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let norm_z = d.const_app(p.norm_sq, &[z]);
    let conj_z = d.const_app(p.conj, &[z]);
    let norm_conj_z = d.const_app(p.norm_sq, &[conj_z]);

    let hypothesis = d.const_app(creal.pos_bound, &[norm_z, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // `bound := CReal.ofRat (Rat.natDivSucc 1 k)` -- the same term
    // `CReal.PosBound`'s own definition uses, built here from the public
    // `CRealPrelude`/`RatPrelude` fields rather than imported from `creal/`.
    let one_nat = d.num(1);
    let gap = d.const_app(creal.rat.nat_div_succ, &[one_nat, k]);
    let bound = d.const_app(creal.of_rat, &[gap]);
    let bound_refl = crefl(d, creal, bound);

    let conj_proof = d.lemma(p.norm_sq_conj, &[z]); // Equiv (normSq (conj z)) (normSq z)
    let swapped = csymm(d, creal, norm_conj_z, norm_z, conj_proof); // Equiv (normSq z) (normSq (conj z))

    // `le_congr : ∀ a b c e, Equiv a b → Equiv c e → le a c → le b e`, at
    // `a = b = bound`, `c = normSq z`, `e = normSq (conj z)`.
    let transported = d.lemma(
        creal.le_congr,
        &[bound, bound, norm_z, norm_conj_z, bound_refl, swapped, h],
    );

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, transported);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(z_fv, carrier, with_k)
    };
    let ty = {
        let conclusion = d.const_app(creal.pos_bound, &[norm_conj_z, k]);
        let inner = d.arrow(hypothesis, conclusion);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(z_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pos_bound_conj,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.conj_inv : ∀ z k (h : CReal.PosBound (normSq z) k),
/// Equiv (conj (inv z k h)) (inv (conj z) k (pos_bound_conj z k h))`.
///
/// Both sides unfold (delta on `conj`/`inv`, iota over `mk`) to a pair of
/// `CReal` expressions in `a := re z`, `b := im z`, `u := CReal.inv (normSq z)
/// k h` and `u' := CReal.inv (normSq (conj z)) k h'`: the left side's
/// components are `a·u` and `−(−(b·u))`, the right side's are `a·u'` and
/// `−((−b)·u')`. `CReal.inv_congr` (independent moduli, both at the same `k`
/// here) relates `u` and `u'` via [`ComplexPrelude::norm_sq_conj`]; the real
/// component is `mul_congr` on that fact directly, and the imaginary
/// component chains two `neg_congr` steps with one ring-calculus double
/// negation.
fn declare_conj_inv(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm_z = d.const_app(p.norm_sq, &[z]);
    let hypothesis = d.const_app(creal.pos_bound, &[norm_z, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let conj_z = d.const_app(p.conj, &[z]);
    let norm_conj_z = d.const_app(p.norm_sq, &[conj_z]);
    let h2 = d.lemma(p.pos_bound_conj, &[z, k, h]); // PosBound (normSq (conj z)) k

    let a = re_of(d, p, z);
    let b = im_of(d, p, z);
    let u = d.const_app(creal.inv, &[norm_z, k, h]);
    let u2 = d.const_app(creal.inv, &[norm_conj_z, k, h2]);

    // `normSq z ~ normSq (conj z)`, then `CReal.inv_congr` at the shared `k`.
    let conj_norm_proof = d.lemma(p.norm_sq_conj, &[z]); // Equiv (normSq (conj z)) (normSq z)
    let norm_swapped = csymm(d, creal, norm_conj_z, norm_z, conj_norm_proof);
    let u_eq = d.lemma(
        creal.inv_congr,
        &[norm_z, norm_conj_z, k, k, h, h2, norm_swapped],
    ); // Equiv u u2

    let refl_a = crefl(d, creal, a);
    let refl_b = crefl(d, creal, b);

    // Real part: Equiv (mul a u) (mul a u2).
    let real_proof = d.lemma(creal.mul_congr, &[a, a, u, u2, refl_a, u_eq]);
    let au = cmul(d, creal, a, u);
    let au2 = cmul(d, creal, a, u2);
    let real_claim = ceq(d, creal, au, au2);

    // Imaginary part: Equiv (neg (neg (mul b u))) (neg (mul (neg b) u2)).
    let mbu_proof = d.lemma(creal.mul_congr, &[b, b, u, u2, refl_b, u_eq]); // Equiv (mul b u)(mul b u2)
    let bu = cmul(d, creal, b, u);
    let bu2 = cmul(d, creal, b, u2);
    let n1 = d.lemma(creal.neg_congr, &[bu, bu2, mbu_proof]); // Equiv (neg bu)(neg bu2)
    let nbu = cneg(d, creal, bu);
    let nbu2 = cneg(d, creal, bu2);
    let n2 = d.lemma(creal.neg_congr, &[nbu, nbu2, n1]); // Equiv (neg(neg bu))(neg(neg bu2))
    let nnbu = cneg(d, creal, nbu);
    let nnbu2 = cneg(d, creal, nbu2);

    let neg_b = cneg(d, creal, b);
    let ring_bridge = ring_proof(
        d,
        creal,
        &RExpr::neg(RExpr::neg(RExpr::mul(RExpr::Atom(b), RExpr::Atom(u2)))),
        &RExpr::neg(RExpr::mul(RExpr::neg(RExpr::Atom(b)), RExpr::Atom(u2))),
    );
    let neg_b_u2 = cmul(d, creal, neg_b, u2);
    let target_imag = cneg(d, creal, neg_b_u2);
    let imag_proof = ctrans(d, creal, nnbu, nnbu2, target_imag, n2, ring_bridge);
    let imag_claim = ceq(d, creal, nnbu, target_imag);

    let body = and_intro(d, p, real_claim, imag_claim, real_proof, imag_proof);

    let inv_z_term = d.const_app(p.inv, &[z, k, h]);
    let conj_inv_z = d.const_app(p.conj, &[inv_z_term]);
    let inv_conj_z = d.const_app(p.inv, &[conj_z, k, h2]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(z_fv, carrier, with_k)
    };
    let ty = {
        let conclusion = zeq(d, p, conj_inv_z, inv_conj_z);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(z_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.conj_inv,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.pow : Complex → Nat → Complex`, by structural `Nat.rec` on the
/// exponent — `pow z Nat.zero ≡ one`, `pow z (Nat.succ j) ≡ mul (pow z j) z`.
///
/// Matches `Int.pow`'s convention verbatim (`int_prelude/defs.rs::declare_pow`):
/// recursion on the exponent, the recursive factor `mul (pow z j) z` with the
/// fresh copy on the RIGHT and the inductive value on the LEFT. `Complex`'s
/// own `mk`-carrying base has to be closed over across the whole `Nat.rec`
/// application, exactly the reason `Int.pow` needed its own helper rather
/// than [`NatOps::define_binary`](crate::nat_prelude::NatOps::define_binary)'s
/// `Nat → Nat → Nat` shape.
fn declare_pow(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = d.kernel().const_(p.one, vec![]);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let body = d.const_app(p.mul, &[ih, z]);
        let inner = d.lam_fv(ih_fv, carrier, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(z_fv, carrier, with_n)
    };
    let ty = {
        let inner = d.arrow(nat, carrier);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pow,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 9),
    })
}

/// `Complex.pow_zero` and `Complex.pow_succ`: the defining equations of
/// [`declare_pow`], each closed by `Eq.refl` alone since `pow`'s `Nat.rec`
/// application ι-reduces on both minor premises — exactly `Int.pow_zero`/
/// `Int.pow_succ`'s own shape (`int_prelude/defs.rs::declare_pow_equations`),
/// with `Eq Complex` in place of `Eq Int`.
fn declare_pow_equations(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    // pow_zero : ∀ z, Eq Complex (pow z Nat.zero) one.
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let zero_n = d.zero();
        let lhs = d.const_app(p.pow, &[z, zero_n]);
        let one = d.kernel().const_(p.one, vec![]);
        let stmt = complex_eq(d, p, lhs, one);
        let proof = complex_eq_refl(d, p, one);
        let value = d.lam_fv(z_fv, carrier, proof);
        let ty = d.pi_fv(z_fv, carrier, stmt);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.pow_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // pow_succ : ∀ z (m : Nat), Eq Complex (pow z (Nat.succ m)) (mul (pow z m) z).
    {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);

        let sm = d.succ(m);
        let lhs = d.const_app(p.pow, &[z, sm]);
        let pm = d.const_app(p.pow, &[z, m]);
        let rhs = d.const_app(p.mul, &[pm, z]);
        let stmt_inner = complex_eq(d, p, lhs, rhs);
        let proof_inner = complex_eq_refl(d, p, rhs);

        let ty = {
            let inner = d.pi_fv(m_fv, nat, stmt_inner);
            d.pi_fv(z_fv, carrier, inner)
        };
        let value = {
            let inner = d.lam_fv(m_fv, nat, proof_inner);
            d.lam_fv(z_fv, carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.pow_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Complex.pow_add : ∀ z (m n : Nat), Equiv (pow z (Nat.add m n))
/// (mul (pow z m) (pow z n))`.
///
/// Induction on `n` via [`NatOps::induct`], mirroring `Int.pow_add`'s own
/// proof shape (`int_prelude/algebra.rs::declare_pow_add`) with every step
/// re-expressed over `Complex.Equiv` in place of `Eq Int`: the base case is
/// [`ComplexPrelude::mul_one`] reversed (`add m Nat.zero` and `pow z
/// Nat.zero` both ι-reduce away), the step lifts the inductive hypothesis
/// through [`ComplexPrelude::mul_congr`] and re-associates with
/// [`ComplexPrelude::mul_assoc`] — no new proof technique.
fn declare_pow_add(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sum = NatOps::add(d, m, x);
        let lhs = d.const_app(p.pow, &[z, sum]);
        let pow_m = d.const_app(p.pow, &[z, m]);
        let pow_x = d.const_app(p.pow, &[z, x]);
        let rhs = d.const_app(p.mul, &[pow_m, pow_x]);
        zeq(d, p, lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            // `pow z (add m 0)` computes to `pow z m`; goal is
            // `Equiv (pow z m) (mul (pow z m) (pow z 0))`, i.e. `mul_one`
            // reversed once `pow z 0` computes to `one`.
            let pow_m = d.const_app(p.pow, &[z, m]);
            let one = d.kernel().const_(p.one, vec![]);
            let product = d.const_app(p.mul, &[pow_m, one]);
            let h = d.lemma(p.mul_one, &[pow_m]); // Equiv (mul pow_m one) pow_m
            d.lemma(p.equiv_symm, &[product, pow_m, h])
        },
        &|d, j, ih| {
            // `pow z (add m (succ j))` computes to `mul (pow z (add m j)) z`.
            let pow_m = d.const_app(p.pow, &[z, m]);
            let pow_j = d.const_app(p.pow, &[z, j]);
            let sum_mj = NatOps::add(d, m, j);
            let pow_sum = d.const_app(p.pow, &[z, sum_mj]);
            let start = d.const_app(p.mul, &[pow_sum, z]);

            let ih_applied = d.const_app(p.mul, &[pow_m, pow_j]);
            let refl_z = d.lemma(p.equiv_refl, &[z]);
            let h_ih = d.lemma(p.mul_congr, &[pow_sum, ih_applied, z, z, ih, refl_z]);
            // h_ih : Equiv (mul pow_sum z) (mul ih_applied z)
            let after_ih = d.const_app(p.mul, &[ih_applied, z]);

            let h_assoc = d.lemma(p.mul_assoc, &[pow_m, pow_j, z]);
            // h_assoc : Equiv (mul (mul pow_m pow_j) z) (mul pow_m (mul pow_j z))
            let inner = d.const_app(p.mul, &[pow_j, z]);
            let end = d.const_app(p.mul, &[pow_m, inner]);

            d.lemma(p.equiv_trans, &[start, after_ih, end, h_ih, h_assoc])
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let inner2 = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(z_fv, carrier, inner2)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let inner2 = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(z_fv, carrier, inner2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.normSq_pow : ∀ z (n : Nat), CReal.Equiv (normSq (pow z n))
/// (CReal.pow (normSq z) n)`.
///
/// Induction on `n` via [`NatOps::induct`], mirroring [`declare_pow_add`]'s
/// own shape but over `CReal.Equiv`: the base case's goal is, up to iota
/// (`pow z Nat.zero ≡ Complex.one`, `CReal.pow (normSq z) Nat.zero ≡
/// CReal.one`), the pure ring identity `CReal.Equiv (CReal.add (CReal.mul
/// CReal.one CReal.one) (CReal.mul CReal.zero CReal.zero)) CReal.one` —
/// `normSq Complex.one` unfolded through `Complex.one`'s own `(one, zero)`
/// pair — closed by [`ring_proof`] exactly as [`ComplexPrelude::i_is_fourth_root`]
/// closes its own fully-iota-reduced product. The step chains
/// [`ComplexPrelude::norm_sq_mul`] (`normSq (mul (pow z j) z) ~ normSq (pow z
/// j) · normSq z`) against the inductive hypothesis via `CReal.mul_congr`,
/// landing exactly on `CReal.pow (normSq z) (Nat.succ j)`'s own iota-reduced
/// shape (`CReal.mul (CReal.pow (normSq z) j) (normSq z)`) with no closing
/// rearrangement needed — the same "no fresh estimate" shape
/// [`ComplexPrelude::root_of_unity_pow`]'s own `pow_mul`-based proof has.
fn declare_norm_sq_pow(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let pow_z_x = d.const_app(p.pow, &[z, x]);
        let norm_pow = d.const_app(p.norm_sq, &[pow_z_x]);
        let norm_z = d.const_app(p.norm_sq, &[z]);
        let pow_norm = d.const_app(creal.pow, &[norm_z, x]);
        ceq(d, creal, norm_pow, pow_norm)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let lhs = RExpr::add(
                RExpr::mul(RExpr::One, RExpr::One),
                RExpr::mul(RExpr::Zero, RExpr::Zero),
            );
            let rhs = RExpr::One;
            ring_proof(d, creal, &lhs, &rhs)
        },
        &|d, j, ih| {
            // ih : CReal.Equiv (normSq (pow z j)) (CReal.pow (normSq z) j)
            let pow_z_j = d.const_app(p.pow, &[z, j]);
            let norm_pow_j = d.const_app(p.norm_sq, &[pow_z_j]);
            let norm_z = d.const_app(p.norm_sq, &[z]);
            let pow_norm_j = d.const_app(creal.pow, &[norm_z, j]);

            // start = normSq (mul (pow z j) z), which is `normSq (pow z
            // (succ j))` up to iota.
            let mul_pow_z = d.const_app(p.mul, &[pow_z_j, z]);
            let start = d.const_app(p.norm_sq, &[mul_pow_z]);

            // Step 1: normSq (mul (pow z j) z) ~ CReal.mul (normSq (pow z j))
            // (normSq z), via `norm_sq_mul`.
            let h1 = d.lemma(p.norm_sq_mul, &[pow_z_j, z]);
            let mid = cmul(d, creal, norm_pow_j, norm_z);

            // Step 2: CReal.mul (normSq (pow z j)) (normSq z) ~
            // CReal.mul (CReal.pow (normSq z) j) (normSq z), via `ih`.
            let refl_norm_z = crefl(d, creal, norm_z);
            let h2 = d.lemma(
                creal.mul_congr,
                &[norm_pow_j, pow_norm_j, norm_z, norm_z, ih, refl_norm_z],
            );
            // end = CReal.mul (CReal.pow (normSq z) j) (normSq z), which is
            // `CReal.pow (normSq z) (succ j)` up to iota.
            let end = cmul(d, creal, pow_norm_j, norm_z);

            ctrans(d, creal, start, mid, end, h1, h2)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(z_fv, carrier, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(z_fv, carrier, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.norm_sq_pow,
        uparams: vec![],
        ty,
        value,
    })
}

// --- finite sums over ℂ, and the geometric series identity ------------------

/// `Complex.sumRange : (Nat → Complex) → Nat → Complex`, structural
/// `Nat.rec` on the bound, matching `Nat.sumRange`'s own convention exactly
/// (`nat_prelude/defs.rs::declare_finite_ranges`): `sumRange f zero ≡ zero`,
/// `sumRange f (succ j) ≡ add (sumRange f j) (f j)` — recursion on the
/// bound, the new term added on the right of the prior sum.
fn declare_sum_range(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = d.kernel().const_(p.zero, vec![]);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let body = d.const_app(p.add, &[ih, fj]);
        let inner = d.lam_fv(ih_fv, carrier, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, carrier);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sum_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 10),
    })
}

/// `Complex.sumRange_zero` and `Complex.sumRange_succ`: the defining
/// equations of [`declare_sum_range`], each closed by `Eq.refl` alone since
/// `sumRange`'s `Nat.rec` application ι-reduces on both minor premises —
/// exactly [`declare_pow_equations`]'s own shape, with `Complex.sumRange` in
/// place of `Complex.pow`.
fn declare_sum_range_equations(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = complex_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    // sumRange_zero : ∀ f, Eq Complex (sumRange f Nat.zero) zero.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero_n = d.zero();
        let lhs = d.const_app(p.sum_range, &[f, zero_n]);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        let stmt = complex_eq(d, p, lhs, zero_c);
        let proof = complex_eq_refl(d, p, zero_c);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_range_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // sumRange_succ : ∀ f (n : Nat),
    //   Eq Complex (sumRange f (succ n)) (add (sumRange f n) (f n)).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = d.const_app(p.sum_range, &[f, sn]);
        let prior = d.const_app(p.sum_range, &[f, n]);
        let fj = d.apply(f, &[n]);
        let rhs = d.const_app(p.add, &[prior, fj]);
        let stmt_inner = complex_eq(d, p, lhs, rhs);
        let proof_inner = complex_eq_refl(d, p, rhs);
        let ty = {
            let inner = d.pi_fv(n_fv, nat, stmt_inner);
            d.pi_fv(f_fv, fn_ty, inner)
        };
        let value = {
            let inner = d.lam_fv(n_fv, nat, proof_inner);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_range_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Complex.sumRange_congr : ∀ f g n, (∀ i, Equiv (f i) (g i)) → Equiv
/// (sumRange f n) (sumRange g n)`.
///
/// Induction on `n` via [`NatOps::induct`], mirroring `Nat.sumRange_congr`'s
/// own proof shape (`nat_prelude/algebra.rs::declare_finite_sum_theorems`)
/// with every step promoted from `Eq Nat` to `Complex.Equiv`: the base case
/// is `Equiv.refl` at `zero` (both sides ι-reduce to it), the step chains a
/// congruence on the prior sums (from the inductive hypothesis) with a
/// congruence on the new terms (from the pointwise hypothesis applied at
/// `j`), both through [`ComplexPrelude::add_congr`].
fn declare_sum_range_congr(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = complex_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let eqv = zeq(d, p, fi, gi);
        d.pi_fv(i_fv, nat, eqv)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.const_app(p.sum_range, &[g, x]);
        zeq(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_c = d.kernel().const_(p.zero, vec![]);
            d.lemma(p.equiv_refl, &[zero_c])
        },
        &|d, j, ih| {
            let f_prior = d.const_app(p.sum_range, &[f, j]);
            let g_prior = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);

            // start = add f_prior fj  ~  mid = add g_prior fj  [congr on ih]
            let start = d.const_app(p.add, &[f_prior, fj]);
            let mid = d.const_app(p.add, &[g_prior, fj]);
            let refl_fj = d.lemma(p.equiv_refl, &[fj]);
            let h1 = d.lemma(p.add_congr, &[f_prior, g_prior, fj, fj, ih, refl_fj]);

            // mid  ~  end = add g_prior gj  [congr on the pointwise hyp at j]
            let end = d.const_app(p.add, &[g_prior, gj]);
            let pointwise_j = d.apply(h, &[j]);
            let refl_g_prior = d.lemma(p.equiv_refl, &[g_prior]);
            let h2 = d.lemma(
                p.add_congr,
                &[g_prior, g_prior, fj, gj, refl_g_prior, pointwise_j],
            );

            d.lemma(p.equiv_trans, &[start, mid, end, h1, h2])
        },
        n,
    );

    let ty = {
        let with_h = d.pi_fv(h_fv, pointwise, stmt);
        let over_n = d.pi_fv(n_fv, nat, with_h);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, pointwise, proof);
        let over_n = d.lam_fv(n_fv, nat, with_h);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.mul_sumRange : ∀ w f n, Equiv (mul w (sumRange f n)) (sumRange
/// (fun i => mul w (f i)) n)` — a constant distributes through a finite sum.
///
/// Induction on `n`, mirroring `Nat.mul_sumRange`'s own proof shape
/// (`nat_prelude/algebra.rs::declare_finite_sum_theorems`): the base case is
/// [`ComplexPrelude::mul_zero`] (both sides ι-reduce to `mul w zero` /
/// `zero` respectively), the step distributes with
/// [`ComplexPrelude::left_distrib`] then lifts the inductive hypothesis
/// through [`ComplexPrelude::add_congr`].
fn declare_mul_sum_range(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let scaled_fn = |d: &mut IntDev<'_>| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = d.const_app(p.mul, &[w, fi]);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs_sum = d.const_app(p.sum_range, &[f, x]);
        let lhs = d.const_app(p.mul, &[w, lhs_sum]);
        let scaled = scaled_fn(d);
        let rhs = d.const_app(p.sum_range, &[scaled, x]);
        zeq(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| d.lemma(p.mul_zero, &[w]),
        &|d, j, ih| {
            let prior = d.const_app(p.sum_range, &[f, j]);
            let fj = d.apply(f, &[j]);
            let extended = d.const_app(p.add, &[prior, fj]);
            let start = d.const_app(p.mul, &[w, extended]);

            let w_prior = d.const_app(p.mul, &[w, prior]);
            let w_fj = d.const_app(p.mul, &[w, fj]);
            let distributed = d.const_app(p.add, &[w_prior, w_fj]);
            let h1 = d.lemma(p.left_distrib, &[w, prior, fj]);

            let scaled = scaled_fn(d);
            let scaled_prior = d.const_app(p.sum_range, &[scaled, j]);
            let end = d.const_app(p.add, &[scaled_prior, w_fj]);
            let refl_wfj = d.lemma(p.equiv_refl, &[w_fj]);
            let h2 = d.lemma(
                p.add_congr,
                &[w_prior, scaled_prior, w_fj, w_fj, ih, refl_wfj],
            );

            d.lemma(p.equiv_trans, &[start, distributed, end, h1, h2])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_f = d.pi_fv(f_fv, fn_ty, over_n);
        d.pi_fv(w_fv, carrier, over_f)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_f = d.lam_fv(f_fv, fn_ty, over_n);
        d.lam_fv(w_fv, carrier, over_f)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_sum_range,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.mul_sub_one_geom : ∀ z (n : Nat), Equiv (mul (add one (neg z))
/// (sumRange (fun k => pow z k) n)) (add one (neg (pow z n)))` — **the
/// geometric series identity**, `(1 − z) · Σ_{k<n} z^k = 1 − z^n`.
///
/// Induction on `n`, telescoping. The base case erases the sum
/// (`sumRange`'s own ι-reduction) and closes with [`ComplexPrelude::mul_zero`]
/// then [`ComplexPrelude::add_neg`] reversed. The step:
///
/// 1. distributes `(1 − z)` over the freshly extended sum with
///    [`ComplexPrelude::left_distrib`];
/// 2. substitutes the inductive hypothesis into the first summand via
///    [`ComplexPrelude::add_congr`];
/// 3. closes the remaining identity `(1 − zⁿ) + (1 − z)·zⁿ = 1 − zⁿ·z` — a
///    pure ring identity once the hypothesis is in place — by the `ring`
///    calculus (`ring_law_proof`) over the atoms `z` and `zⁿ`, exactly the
///    decision procedure [`declare_ring_laws`] uses, applied to one specific
///    instance rather than to declare a new named law.
fn declare_mul_sub_one_geom(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_z = d.const_app(p.neg, &[z]);
    let a = d.const_app(p.add, &[one, neg_z]); // a = 1 - z

    let pow_fn = |d: &mut IntDev<'_>| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = d.const_app(p.pow, &[z, i]);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let f = pow_fn(d);
        let sum = d.const_app(p.sum_range, &[f, x]);
        let lhs = d.const_app(p.mul, &[a, sum]);
        let pow_x = d.const_app(p.pow, &[z, x]);
        let neg_pow_x = d.const_app(p.neg, &[pow_x]);
        let rhs = d.const_app(p.add, &[one, neg_pow_x]);
        zeq(d, p, lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            // Goal, after ι on both `sumRange f zero` and `pow z zero`:
            // Equiv (mul a zero) (add one (neg one)).
            let zero_c = d.kernel().const_(p.zero, vec![]);
            let neg_one = d.const_app(p.neg, &[one]);
            let add_one_neg_one = d.const_app(p.add, &[one, neg_one]);
            let mul_a_zero = d.const_app(p.mul, &[a, zero_c]);

            let mul_zero_h = d.lemma(p.mul_zero, &[a]); // Equiv mul_a_zero zero_c
            let add_neg_h = d.lemma(p.add_neg, &[one]); // Equiv add_one_neg_one zero_c
            let sym = d.lemma(p.equiv_symm, &[add_one_neg_one, zero_c, add_neg_h]);
            d.lemma(
                p.equiv_trans,
                &[mul_a_zero, zero_c, add_one_neg_one, mul_zero_h, sym],
            )
        },
        &|d, j, ih| {
            // ih : Equiv (mul a (sumRange f j)) (add one (neg (pow z j)))
            let zn = d.const_app(p.pow, &[z, j]);
            let s_j = {
                let f = pow_fn(d);
                d.const_app(p.sum_range, &[f, j])
            };
            let extended = d.const_app(p.add, &[s_j, zn]);
            let start = d.const_app(p.mul, &[a, extended]);

            // start ~ distributed = add (mul a s_j) (mul a zn)  [left_distrib]
            let a_s_j = d.const_app(p.mul, &[a, s_j]);
            let a_zn = d.const_app(p.mul, &[a, zn]);
            let distributed = d.const_app(p.add, &[a_s_j, a_zn]);
            let h1 = d.lemma(p.left_distrib, &[a, s_j, zn]);

            // distributed ~ after_ih = add (add one (neg zn)) (mul a zn)
            //   [substitute ih into the first summand]
            let neg_zn = d.const_app(p.neg, &[zn]);
            let one_minus_zn = d.const_app(p.add, &[one, neg_zn]);
            let after_ih = d.const_app(p.add, &[one_minus_zn, a_zn]);
            let refl_a_zn = d.lemma(p.equiv_refl, &[a_zn]);
            let h2 = d.lemma(
                p.add_congr,
                &[a_s_j, one_minus_zn, a_zn, a_zn, ih, refl_a_zn],
            );

            // after_ih ~ end = add one (neg (mul zn z))  [pure ring identity]
            let z_cexpr = CExpr::var(d, p, z);
            let zn_cexpr = CExpr::var(d, p, zn);
            let a_cexpr = CExpr::add(CExpr::One, CExpr::neg(z_cexpr.clone()));
            let lhs_cexpr = CExpr::add(
                CExpr::add(CExpr::One, CExpr::neg(zn_cexpr.clone())),
                CExpr::mul(a_cexpr, zn_cexpr.clone()),
            );
            let rhs_cexpr = CExpr::add(
                CExpr::One,
                CExpr::neg(CExpr::mul(zn_cexpr.clone(), z_cexpr.clone())),
            );
            let end_final = render_c(d, p, &rhs_cexpr);
            let h3 = ring_law_proof(d, p, &lhs_cexpr, &rhs_cexpr);

            let h_mid = d.lemma(p.equiv_trans, &[start, distributed, after_ih, h1, h2]);
            d.lemma(p.equiv_trans, &[start, after_ih, end_final, h_mid, h3])
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        d.pi_fv(z_fv, carrier, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        d.lam_fv(z_fv, carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_sub_one_geom,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.geom_series_div : ∀ z (n k : Nat) (h : CReal.PosBound (normSq
/// (add one (neg z))) k), Equiv (sumRange (fun j => pow z j) n) (div (add one
/// (neg (pow z n))) (add one (neg z)) k h)` — the quotient form of
/// [`declare_mul_sub_one_geom`], with the modulus witness for `1 − z` taken as
/// an explicit argument (never derived from `z ≁ 1`, which this kernel cannot
/// do without Markov's principle).
///
/// Cancels `a := 1 − z` against `c := inv a k h` on the left of `mul a
/// (sumRange …)`: `c·(a·S) ~ (c·a)·S ~ 1·S ~ S` via
/// [`ComplexPrelude::inv_mul_cancel`]/[`ComplexPrelude::mul_assoc`]/
/// [`ComplexPrelude::mul_comm`]/[`ComplexPrelude::mul_one`], then substitutes
/// [`ComplexPrelude::mul_sub_one_geom`] for `a·S` and reads the result
/// backwards, closing at `div`'s own definitional unfolding
/// (`div x y k h ≡ mul x (inv y k h)`).
fn declare_geom_series_div(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_z = d.const_app(p.neg, &[z]);
    let a = d.const_app(p.add, &[one, neg_z]); // a = 1 - z
    let norm_a = d.const_app(p.norm_sq, &[a]);
    let hypothesis = d.const_app(creal.pos_bound, &[norm_a, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let c = d.const_app(p.inv, &[a, k, h]); // c = (1 - z)^-1

    let pow_fn = |d: &mut IntDev<'_>| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = d.const_app(p.pow, &[z, i]);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };
    let f = pow_fn(d);
    let s = d.const_app(p.sum_range, &[f, n]); // s = sumRange (pow z .) n

    let pow_n = d.const_app(p.pow, &[z, n]);
    let neg_pow_n = d.const_app(p.neg, &[pow_n]);
    let rhs_geom = d.const_app(p.add, &[one, neg_pow_n]); // 1 - z^n

    let div_term = d.const_app(p.div, &[rhs_geom, a, k, h]);
    let stmt = zeq(d, p, s, div_term);

    // h_geom : Equiv (mul a s) rhs_geom
    let h_geom = d.lemma(p.mul_sub_one_geom, &[z, n]);

    let a_s = d.const_app(p.mul, &[a, s]);
    let c_as = d.const_app(p.mul, &[c, a_s]);
    let c_rhs = d.const_app(p.mul, &[c, rhs_geom]);
    let refl_c = d.lemma(p.equiv_refl, &[c]);
    let cong_h = d.lemma(p.mul_congr, &[c, c, a_s, rhs_geom, refl_c, h_geom]);
    // cong_h : Equiv c_as c_rhs

    let c_a = d.const_app(p.mul, &[c, a]);
    let inv_mul_h = d.lemma(p.inv_mul_cancel, &[a, k, h]); // Equiv c_a one
    let ca_s = d.const_app(p.mul, &[c_a, s]);
    let one_s = d.const_app(p.mul, &[one, s]);
    let refl_s = d.lemma(p.equiv_refl, &[s]);
    let step_b = d.lemma(p.mul_congr, &[c_a, one, s, s, inv_mul_h, refl_s]);
    // step_b : Equiv ca_s one_s

    let assoc = d.lemma(p.mul_assoc, &[c, a, s]); // Equiv ca_s c_as
    let assoc_symm = d.lemma(p.equiv_symm, &[ca_s, c_as, assoc]); // Equiv c_as ca_s

    let collapse = d.lemma(p.equiv_trans, &[c_as, ca_s, one_s, assoc_symm, step_b]);
    // collapse : Equiv c_as one_s

    let s_one = d.const_app(p.mul, &[s, one]);
    let comm_one_s = d.lemma(p.mul_comm, &[one, s]); // Equiv one_s s_one
    let mul_one_s = d.lemma(p.mul_one, &[s]); // Equiv s_one s
    let f_step = d.lemma(p.equiv_trans, &[one_s, s_one, s, comm_one_s, mul_one_s]);
    // f_step : Equiv one_s s

    let reduce = d.lemma(p.equiv_trans, &[c_as, one_s, s, collapse, f_step]);
    // reduce : Equiv c_as s
    let reduce_symm = d.lemma(p.equiv_symm, &[c_as, s, reduce]); // Equiv s c_as

    let step_i = d.lemma(p.equiv_trans, &[s, c_as, c_rhs, reduce_symm, cong_h]);
    // step_i : Equiv s c_rhs

    let rhs_c = d.const_app(p.mul, &[rhs_geom, c]);
    let comm_final = d.lemma(p.mul_comm, &[c, rhs_geom]); // Equiv c_rhs rhs_c
    let final_proof = d.lemma(p.equiv_trans, &[s, c_rhs, rhs_c, step_i, comm_final]);
    // final_proof : Equiv s rhs_c, and div_term ≡ rhs_c by δ/β on `div`.

    let ty = {
        let inner = d.pi_fv(h_fv, hypothesis, stmt);
        let with_k = d.pi_fv(k_fv, nat, inner);
        let with_n = d.pi_fv(n_fv, nat, with_k);
        d.pi_fv(z_fv, carrier, with_n)
    };
    let value = {
        let inner = d.lam_fv(h_fv, hypothesis, final_proof);
        let with_k = d.lam_fv(k_fv, nat, inner);
        let with_n = d.lam_fv(n_fv, nat, with_k);
        d.lam_fv(z_fv, carrier, with_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_series_div,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the ℕ → ℂ cast ----------------------------------------------------------

/// `Complex.ofNat`, by structural `Nat.rec` on the argument, exactly
/// [`declare_pow`]/[`declare_sum_range`]'s own recursion shape (`d.prelude().rec`
/// is `Nat.rec`, not [`ComplexPrelude::rec`]).
fn declare_of_nat(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();

    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = d.kernel().const_(p.zero, vec![]);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let one = d.kernel().const_(p.one, vec![]);
        let body = d.const_app(p.add, &[ih, one]);
        let inner = d.lam_fv(ih_fv, carrier, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.of_nat,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 11),
    })
}

/// `Complex.ofNat_zero` and `Complex.ofNat_succ`: the defining equations of
/// [`declare_of_nat`], each closed by `Eq.refl` alone since `ofNat`'s
/// `Nat.rec` application ι-reduces on both minor premises — exactly
/// [`declare_pow_equations`]'s own shape.
fn declare_of_nat_equations(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    // of_nat_zero : Eq Complex (ofNat Nat.zero) zero.
    {
        let zero_n = d.zero();
        let lhs = d.const_app(p.of_nat, &[zero_n]);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        let stmt = complex_eq(d, p, lhs, zero_c);
        let proof = complex_eq_refl(d, p, zero_c);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.of_nat_zero,
            uparams: vec![],
            ty: stmt,
            value: proof,
        })?;
    }

    // of_nat_succ : ∀ n, Eq Complex (ofNat (Nat.succ n)) (add (ofNat n) one).
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = d.const_app(p.of_nat, &[sn]);
        let of_n = d.const_app(p.of_nat, &[n]);
        let one = d.kernel().const_(p.one, vec![]);
        let rhs = d.const_app(p.add, &[of_n, one]);
        let stmt_inner = complex_eq(d, p, lhs, rhs);
        let proof_inner = complex_eq_refl(d, p, rhs);
        let ty = d.pi_fv(n_fv, nat, stmt_inner);
        let value = d.lam_fv(n_fv, nat, proof_inner);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.of_nat_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Complex.ofNat_add : ∀ m n, Equiv (ofNat (Nat.add m n)) (add (ofNat m)
/// (ofNat n))`.
///
/// Induction on `n`, mirroring [`declare_pow_add`]'s own proof shape with
/// `add`/`add_assoc`/`add_congr` in place of `mul`/`mul_assoc`/`mul_congr`:
/// the base case is [`ComplexPrelude::add_zero`] reversed (`add m Nat.zero`
/// and `ofNat Nat.zero` both ι-reduce away), the step lifts the inductive
/// hypothesis through [`ComplexPrelude::add_congr`] then re-associates with
/// [`ComplexPrelude::add_assoc`].
fn declare_of_nat_add(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sum = NatOps::add(d, m, x);
        let lhs = d.const_app(p.of_nat, &[sum]);
        let of_m = d.const_app(p.of_nat, &[m]);
        let of_x = d.const_app(p.of_nat, &[x]);
        let rhs = d.const_app(p.add, &[of_m, of_x]);
        zeq(d, p, lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let of_m = d.const_app(p.of_nat, &[m]);
            let zero_c = d.kernel().const_(p.zero, vec![]);
            let sum = d.const_app(p.add, &[of_m, zero_c]);
            let h = d.lemma(p.add_zero, &[of_m]); // Equiv(add(of_m,zero), of_m)
            d.lemma(p.equiv_symm, &[sum, of_m, h])
        },
        &|d, j, ih| {
            // `ofNat(add m (succ j))` ι-reduces to `add(ofNat(add m j), one)`;
            // `add(ofNat m, ofNat(succ j))` ι-reduces to
            // `add(ofNat m, add(ofNat j, one))`.
            let of_m = d.const_app(p.of_nat, &[m]);
            let of_j = d.const_app(p.of_nat, &[j]);
            let one = d.kernel().const_(p.one, vec![]);
            let sum_mj = NatOps::add(d, m, j);
            let of_sum_mj = d.const_app(p.of_nat, &[sum_mj]);
            let start = d.const_app(p.add, &[of_sum_mj, one]);

            let ih_applied = d.const_app(p.add, &[of_m, of_j]);
            let refl_one = d.lemma(p.equiv_refl, &[one]);
            let h_ih = d.lemma(
                p.add_congr,
                &[of_sum_mj, ih_applied, one, one, ih, refl_one],
            );
            let after_ih = d.const_app(p.add, &[ih_applied, one]);

            let h_assoc = d.lemma(p.add_assoc, &[of_m, of_j, one]);
            let inner = d.const_app(p.add, &[of_j, one]);
            let end = d.const_app(p.add, &[of_m, inner]);

            d.lemma(p.equiv_trans, &[start, after_ih, end, h_ih, h_assoc])
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        d.pi_fv(m_fv, nat, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        d.lam_fv(m_fv, nat, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_nat_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.ofNat_mul : ∀ m n, Equiv (ofNat (Nat.mul m n)) (mul (ofNat m)
/// (ofNat n))`.
///
/// Induction on `n`. The base case is [`ComplexPrelude::mul_zero`] reversed.
/// The step unfolds `Nat.mul m (Nat.succ j)` to `Nat.add (Nat.mul m j) m`
/// (`Nat.mul`'s own ι-step), applies [`ComplexPrelude::of_nat_add`] to cast
/// that sum, substitutes the inductive hypothesis via
/// [`ComplexPrelude::add_congr`], then matches the `ofNat (Nat.succ j)`
/// -unfolded right-hand side via [`ComplexPrelude::left_distrib`] and
/// [`ComplexPrelude::mul_one`].
fn declare_of_nat_mul(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let prod = NatOps::mul(d, m, x);
        let lhs = d.const_app(p.of_nat, &[prod]);
        let of_m = d.const_app(p.of_nat, &[m]);
        let of_x = d.const_app(p.of_nat, &[x]);
        let rhs = d.const_app(p.mul, &[of_m, of_x]);
        zeq(d, p, lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let of_m = d.const_app(p.of_nat, &[m]);
            let zero_c = d.kernel().const_(p.zero, vec![]);
            let prod = d.const_app(p.mul, &[of_m, zero_c]);
            let h = d.lemma(p.mul_zero, &[of_m]); // Equiv(mul(of_m,zero), zero)
            d.lemma(p.equiv_symm, &[prod, zero_c, h])
        },
        &|d, j, ih| {
            let of_m = d.const_app(p.of_nat, &[m]);
            let of_j = d.const_app(p.of_nat, &[j]);
            let one = d.kernel().const_(p.one, vec![]);

            // start ≡ ofNat(mul m (succ j)) by one ι-step of `Nat.mul`.
            let mul_mj = NatOps::mul(d, m, j);
            let of_mul_mj = d.const_app(p.of_nat, &[mul_mj]);
            let sum_nat = NatOps::add(d, mul_mj, m);
            let start = d.const_app(p.of_nat, &[sum_nat]);

            // Step 1: `of_nat_add` unfolds the cast sum.
            let h1 = d.lemma(p.of_nat_add, &[mul_mj, m]);
            let after1 = d.const_app(p.add, &[of_mul_mj, of_m]);

            // Step 2: substitute the inductive hypothesis.
            let ih_applied = d.const_app(p.mul, &[of_m, of_j]);
            let refl_of_m = d.lemma(p.equiv_refl, &[of_m]);
            let h2 = d.lemma(
                p.add_congr,
                &[of_mul_mj, ih_applied, of_m, of_m, ih, refl_of_m],
            );
            let after2 = d.const_app(p.add, &[ih_applied, of_m]);

            // Right-hand side, reduced: `mul(ofNat m, ofNat(succ j))` ι-reduces
            // to `mul(of_m, add(of_j, one))`.
            let of_sj = d.const_app(p.add, &[of_j, one]);
            let rhs_reduced = d.const_app(p.mul, &[of_m, of_sj]);

            // `left_distrib(of_m, of_j, one)`.
            let h3 = d.lemma(p.left_distrib, &[of_m, of_j, one]);
            let mul_of_m_one = d.const_app(p.mul, &[of_m, one]);
            let after3 = d.const_app(p.add, &[ih_applied, mul_of_m_one]);

            // `mul_one(of_m)` closes the second summand.
            let h4 = d.lemma(p.mul_one, &[of_m]);
            let refl_ih_applied = d.lemma(p.equiv_refl, &[ih_applied]);
            let h5 = d.lemma(
                p.add_congr,
                &[
                    ih_applied,
                    ih_applied,
                    mul_of_m_one,
                    of_m,
                    refl_ih_applied,
                    h4,
                ],
            );
            // h5 : Equiv(after3, after2)

            let h5_symm = d.lemma(p.equiv_symm, &[after3, after2, h5]);
            let h3_symm = d.lemma(p.equiv_symm, &[rhs_reduced, after3, h3]);

            let t1 = d.lemma(p.equiv_trans, &[start, after1, after2, h1, h2]);
            let t2 = d.lemma(p.equiv_trans, &[start, after2, after3, t1, h5_symm]);
            d.lemma(p.equiv_trans, &[start, after3, rhs_reduced, t2, h3_symm])
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        d.pi_fv(m_fv, nat, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        d.lam_fv(m_fv, nat, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_nat_mul,
        uparams: vec![],
        ty,
        value,
    })
}

// --- finite sums' additive homomorphism, and a bounded reindex --------------

/// `Complex.sumRange_add : ∀ f g n, Equiv (sumRange (fun i => add (f i) (g
/// i)) n) (add (sumRange f n) (sumRange g n))`.
///
/// Induction on `n`, mirroring `Nat.sumRange_add`'s own proof shape
/// (`nat_prelude/binomial.rs::declare_sum_range_add`); the successor case's
/// four-term rearrangement `(A+B)+(C+D) ~ (A+C)+(B+D)` closes by
/// `ring_law_proof` over the four summands as opaque atoms, in place of a
/// hand-built `add_add_add_comm` — the decision procedure the ℕ proof did not
/// have available.
fn declare_sum_range_add(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let combined_fn = |d: &mut IntDev<'_>, f: ExprId, g: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let body = d.const_app(p.add, &[fi, gi]);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let combined = combined_fn(d, f, g);
        let lhs = d.const_app(p.sum_range, &[combined, x]);
        let sf = d.const_app(p.sum_range, &[f, x]);
        let sg = d.const_app(p.sum_range, &[g, x]);
        let rhs = d.const_app(p.add, &[sf, sg]);
        zeq(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_c = d.kernel().const_(p.zero, vec![]);
            let sum = d.const_app(p.add, &[zero_c, zero_c]);
            let h = d.lemma(p.add_zero, &[zero_c]); // Equiv(add(zero,zero), zero)
            d.lemma(p.equiv_symm, &[sum, zero_c, h])
        },
        &|d, j, ih| {
            let combined = combined_fn(d, f, g);
            let combined_j = d.apply(combined, &[j]);
            let prior_combined = d.const_app(p.sum_range, &[combined, j]);
            let start = d.const_app(p.add, &[prior_combined, combined_j]);

            let sf_j = d.const_app(p.sum_range, &[f, j]);
            let sg_j = d.const_app(p.sum_range, &[g, j]);
            let sfg = d.const_app(p.add, &[sf_j, sg_j]);
            let refl_combined_j = d.lemma(p.equiv_refl, &[combined_j]);
            let h1 = d.lemma(
                p.add_congr,
                &[
                    prior_combined,
                    sfg,
                    combined_j,
                    combined_j,
                    ih,
                    refl_combined_j,
                ],
            );
            let after_ih = d.const_app(p.add, &[sfg, combined_j]);

            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);

            let sf_j_v = CExpr::var(d, p, sf_j);
            let sg_j_v = CExpr::var(d, p, sg_j);
            let fj_v = CExpr::var(d, p, fj);
            let gj_v = CExpr::var(d, p, gj);
            let lhs_c = CExpr::add(
                CExpr::add(sf_j_v.clone(), sg_j_v.clone()),
                CExpr::add(fj_v.clone(), gj_v.clone()),
            );
            let rhs_c = CExpr::add(CExpr::add(sf_j_v, fj_v), CExpr::add(sg_j_v, gj_v));
            let end_proof = ring_law_proof(d, p, &lhs_c, &rhs_c);
            let end_term = render_c(d, p, &rhs_c);

            d.lemma(p.equiv_trans, &[start, after_ih, end_term, h1, end_proof])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.sumRange_shiftFront : ∀ f n, Equiv (sumRange f (Nat.succ n)) (add
/// (f Nat.zero) (sumRange (fun k => f (Nat.succ k)) n))` — peeling the FRONT
/// term off a finite sum.
///
/// Induction on `n`, mirroring `Nat.sumRange_shiftFront`'s own proof shape
/// (`nat_prelude/binomial.rs::declare_sum_range_shift_front`). Unlike the ℕ
/// version's `zero_add`, the base case here needs [`ComplexPrelude::add_comm`]
/// (not a reversed [`ComplexPrelude::add_zero`]): `Complex.add` is not
/// structurally recursive, so `add zero_c f0` and `add f0 zero_c` are each
/// only ι-reduced this far, not to `f0` itself.
fn declare_sum_range_shift_front(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let shifted_fn = |d: &mut IntDev<'_>, f: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let body = d.apply(f, &[sk]);
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sx = d.succ(x);
        let lhs = d.const_app(p.sum_range, &[f, sx]);
        let zero = d.zero();
        let f0 = d.apply(f, &[zero]);
        let shifted = shifted_fn(d, f);
        let sr = d.const_app(p.sum_range, &[shifted, x]);
        let rhs = d.const_app(p.add, &[f0, sr]);
        zeq(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let f0 = d.apply(f, &[zero_n]);
            let zero_c = d.kernel().const_(p.zero, vec![]);
            d.lemma(p.add_comm, &[zero_c, f0])
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let f_prior_succ = d.const_app(p.sum_range, &[f, sj]);
            let f_sj = d.apply(f, &[sj]);
            let start = d.const_app(p.add, &[f_prior_succ, f_sj]);

            let zero_n = d.zero();
            let f0 = d.apply(f, &[zero_n]);
            let shifted = shifted_fn(d, f);
            let shifted_j = d.const_app(p.sum_range, &[shifted, j]);
            let mid1 = d.const_app(p.add, &[f0, shifted_j]);
            let refl_f_sj = d.lemma(p.equiv_refl, &[f_sj]);
            let h1 = d.lemma(
                p.add_congr,
                &[f_prior_succ, mid1, f_sj, f_sj, ih, refl_f_sj],
            );
            let after_ih = d.const_app(p.add, &[mid1, f_sj]);

            let inner = d.const_app(p.add, &[shifted_j, f_sj]);
            let end = d.const_app(p.add, &[f0, inner]);
            let h2 = d.lemma(p.add_assoc, &[f0, shifted_j, f_sj]);

            d.lemma(p.equiv_trans, &[start, after_ih, end, h1, h2])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_shift_front,
        uparams: vec![],
        ty,
        value,
    })
}

/// `fun i => Nat.lt i bound → Equiv (f i) (g i)`.
fn bounded_pointwise_complex(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    f: ExprId,
    g: ExprId,
    bound: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let eqn = zeq(d, p, fi, gi);
    let body = d.arrow(hyp, eqn);
    d.pi_fv(i_fv, nat, body)
}

/// `Complex.sumRange_congr_lt : ∀ f g n, (∀ i, Nat.lt i n → Equiv (f i) (g
/// i)) → Equiv (sumRange f n) (sumRange g n)` — [`ComplexPrelude::sum_range_congr`]
/// with the hypothesis weakened to indices below the bound.
///
/// Induction on `n`, mirroring `Nat.sumRange_congr_lt`'s own proof shape
/// (`nat_prelude/binomial.rs::declare_sum_range_congr_lt`).
fn declare_sum_range_congr_lt(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_pointwise_complex(d, p, f, g, x);
        let lhs = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.const_app(p.sum_range, &[g, x]);
        let eqn = zeq(d, p, lhs, rhs);
        d.arrow(hyp, eqn)
    };
    let stmt = motive(d, n);

    let nat_p = d.prelude();

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = bounded_pointwise_complex(d, p, f, g, zero);
            let h_fv = d.fresh_fvar();
            let zero_c = d.kernel().const_(p.zero, vec![]);
            let body = d.lemma(p.equiv_refl, &[zero_c]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_pointwise_complex(d, p, f, g, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let h_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let le_succ_j = d.lemma(nat_p.le_succ, &[j]);
                let lifted = d.lemma(nat_p.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let lt_j_sj = d.lemma(nat_p.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let f_prior = d.const_app(p.sum_range, &[f, j]);
            let g_prior = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let start = d.const_app(p.add, &[f_prior, fj]);
            let mid = d.const_app(p.add, &[g_prior, fj]);
            let refl_fj = d.lemma(p.equiv_refl, &[fj]);
            let h1 = d.lemma(p.add_congr, &[f_prior, g_prior, fj, fj, sub1, refl_fj]);
            let end = d.const_app(p.add, &[g_prior, gj]);
            let refl_g_prior = d.lemma(p.equiv_refl, &[g_prior]);
            let h2 = d.lemma(p.add_congr, &[g_prior, g_prior, fj, gj, refl_g_prior, sub2]);
            let body = d.lemma(p.equiv_trans, &[start, mid, end, h1, h2]);

            d.lam_fv(h_fv, hyp_ty, body)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_congr_lt,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.sumRange_split : ∀ f m n, Equiv (sumRange f (Nat.add m n)) (add
/// (sumRange f m) (sumRange (fun k => f (Nat.add m k)) n))`.
///
/// Induction on `n`, mirroring [`CRealPrelude::sum_range_split`]'s own proof
/// shape (`creal/series.rs::declare_sum_range_split`) verbatim with every
/// step promoted from `CReal.Equiv` to `Complex.Equiv`: both cases close
/// purely by `Nat.add`'s own iota-reduction (`add m Nat.zero ≡ m`, `add m
/// (Nat.succ j) ≡ Nat.succ (add m j)`) plus one
/// [`ComplexPrelude::add_zero`]/[`ComplexPrelude::add_assoc`] respectively —
/// no ring calculus needed, the same reason the `CReal` original needs none.
fn declare_sum_range_split(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let shifted_fn = |d: &mut IntDev<'_>, m: ExprId, f: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let m_plus_k = NatOps::add(d, m, k);
        let body = d.apply(f, &[m_plus_k]);
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, body)
    };

    let sum_f_m = d.const_app(p.sum_range, &[f, m]);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let m_plus_x = NatOps::add(d, m, x);
        let lhs = d.const_app(p.sum_range, &[f, m_plus_x]);
        let h = shifted_fn(d, m, f);
        let sum_h_x = d.const_app(p.sum_range, &[h, x]);
        let rhs = d.const_app(p.add, &[sum_f_m, sum_h_x]);
        zeq(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_c = d.kernel().const_(p.zero, vec![]);
            let padded = d.const_app(p.add, &[sum_f_m, zero_c]);
            let h = d.lemma(p.add_zero, &[sum_f_m]); // Equiv padded sum_f_m
            d.lemma(p.equiv_symm, &[padded, sum_f_m, h])
        },
        &|d, j, ih| {
            // ih : Equiv (sumRange f (add m j)) (add sum_f_m (sumRange h j))
            let h = shifted_fn(d, m, f);
            let sum_h_j = d.const_app(p.sum_range, &[h, j]);
            let m_plus_j = NatOps::add(d, m, j);
            let fmj = d.apply(f, &[m_plus_j]); // = f (add m j) = h j, up to beta

            let sum_f_mj = d.const_app(p.sum_range, &[f, m_plus_j]);
            let start = d.const_app(p.add, &[sum_f_mj, fmj]); // = sumRange f (add m (succ j)), up to iota

            let rhs_prior = d.const_app(p.add, &[sum_f_m, sum_h_j]);
            let refl_fmj = d.lemma(p.equiv_refl, &[fmj]);
            let h1 = d.lemma(p.add_congr, &[sum_f_mj, rhs_prior, fmj, fmj, ih, refl_fmj]);
            let after_ih = d.const_app(p.add, &[rhs_prior, fmj]);

            let sum_h_j_plus_fmj = d.const_app(p.add, &[sum_h_j, fmj]);
            let target = d.const_app(p.add, &[sum_f_m, sum_h_j_plus_fmj]);
            let h2 = d.lemma(p.add_assoc, &[sum_f_m, sum_h_j, fmj]);

            d.lemma(p.equiv_trans, &[start, after_ih, target, h1, h2])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        d.pi_fv(f_fv, fn_ty, over_m)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        d.lam_fv(f_fv, fn_ty, over_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_split,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the binomial theorem ----------------------------------------------------
//
// The exponent, the summation bound, `Nat.choose` and `Nat.sub` are `Nat`
// throughout, exactly mirroring `nat_prelude/binomial.rs::declare_add_pow`'s
// own development one layer up: only the coefficient `Nat.choose n k` is cast
// into `Complex` (via [`ComplexPrelude::of_nat`]), and the ring elements `a`,
// `b` range over `Complex`. Every `Nat`-side fact the ℕ proof used
// (`choose_succ_succ`, `succ_sub_succ`, `choose_succ_self_eq_zero`,
// `choose_zero_right`, and the private `sub_succ_of_lt`, rebuilt here as
// [`nat_sub_succ_of_lt`] from public primitives since `nat_prelude` is a live
// lane's directory) is PUBLIC `Nat` prelude surface, lifted into a `Complex`
// context by `nat_eq_to_complex_equiv`. Every pure algebraic rearrangement
// the ℕ proof derived by hand (`mul_left_comm`, `add_left_comm`, and the
// multi-step `mul_assoc`/`mul_comm`/`left_distrib` chains inside
// `pascal_split_term`/`b_side_term`) is instead decided by `ring_law_proof`
// over the relevant atoms.

/// `Eq.rec.{0,1} Complex p motive refl_case q h` — the `Complex` counterpart
/// of `IntDev::itransport` (`int_prelude/ops.rs`), needed because
/// [`ComplexPrelude::pow_succ`]/[`ComplexPrelude::pow_zero`] are stated over
/// `Eq Complex`, not `Complex.Equiv`.
fn complex_transport(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    motive: ExprId,
    refl_case: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let zero = d.kernel().level_zero();
    let one = d.level_one();
    let name = p.creal.rat.int.logic.eq_rec;
    let rec = d.kernel().const_(name, vec![zero, one]);
    let carrier = complex_ty(d, p);
    d.apply(rec, &[carrier, a, motive, refl_case, q, h])
}

/// `fun (x : Complex) (_ : Eq Complex a x) => body(x)`.
fn complex_eq_motive(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let concl = body(d, x);
    let hyp = complex_eq(d, p, a, x);
    let anon = d.anon_name();
    let inner = d.kernel().lam(anon, hyp, concl, BinderInfo::Default);
    let carrier = complex_ty(d, p);
    d.lam_fv(x_fv, carrier, inner)
}

/// From `h : Eq Complex a b`, derive `Equiv a b`. `Equiv` is reflexive, so
/// this is `Eq.rec` with motive `fun y _ => Equiv a y`, base case `Equiv.refl
/// a`.
fn complex_eq_to_equiv(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let motive = complex_eq_motive(d, p, a, &|d, x| zeq(d, p, a, x));
    let refl_case = d.lemma(p.equiv_refl, &[a]);
    complex_transport(d, p, a, motive, refl_case, b, h)
}

/// From `h : Eq Nat a b`, derive `Equiv (f a) (f b)` for any `Complex`-valued
/// context `f` over a natural — the Nat-to-Complex analogue of
/// `IntDev::nat_eq_to_int` (`int_prelude/ops.rs`), built over `Complex.Equiv`
/// rather than `Eq Int` since `Eq Complex` is not the equality of complex
/// numbers.
fn nat_eq_to_complex_equiv(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.eq_motive(a, &|d, x| {
        let fx = f(d, x);
        zeq(d, p, fa, fx)
    });
    let refl_case = d.lemma(p.equiv_refl, &[fa]);
    d.transport(a, motive, refl_case, b, h)
}

/// `(ofNat (choose row k) * a^k) * b^(row-k)` — the summand of the binomial
/// expansion at `row`, at a POINT.
fn binom_term_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    row: ExprId,
    k: ExprId,
) -> ExprId {
    let c = d.choose(row, k);
    let of_c = d.const_app(p.of_nat, &[c]);
    let ak = d.const_app(p.pow, &[a, k]);
    let c_ak = d.const_app(p.mul, &[of_c, ak]);
    let sub_rk = d.sub(row, k);
    let b_pow = d.const_app(p.pow, &[b, sub_rk]);
    d.const_app(p.mul, &[c_ak, b_pow])
}

/// `fun k => binom_term_c a b row k`, as a lambda.
fn binom_term_fn_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    row: ExprId,
) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = binom_term_c(d, p, a, b, row, k);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `sumRange (fun k => binom_term_c a b row k) (succ row)` — the sum-form of
/// `(a+b)^row`.
fn binom_sum_c(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, b: ExprId, row: ExprId) -> ExprId {
    let t = binom_term_fn_c(d, p, a, b, row);
    let srow = d.succ(row);
    d.const_app(p.sum_range, &[t, srow])
}

/// `(choose n (succ k) * a^(succ k)) * b^(n-k)` — the second summand of
/// Pascal's split of `binom_term_c a b (succ n) (succ k)`.
fn pascal_tail_term_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    k: ExprId,
) -> ExprId {
    let sk = d.succ(k);
    let c = d.choose(n, sk);
    let of_c = d.const_app(p.of_nat, &[c]);
    let ak = d.const_app(p.pow, &[a, sk]);
    let c_ak = d.const_app(p.mul, &[of_c, ak]);
    let sub_nk = d.sub(n, k);
    let b_pow = d.const_app(p.pow, &[b, sub_nk]);
    d.const_app(p.mul, &[c_ak, b_pow])
}

/// `fun k => pascal_tail_term_c a b n k`, built directly (not via `apply`),
/// so it matches the reduced shape [`pascal_split_term_c`] proves pointwise
/// identities against.
fn pascal_tail_fn_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = pascal_tail_term_c(d, p, a, b, n, k);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Equiv (binom_term_c a b (succ n) (succ k)) (add (mul a (binom_term_c a b
/// n k)) (pascal_tail_term_c a b n k))`, for ALL `k` — unconditional, needing
/// only the public `Nat.choose_succ_succ` (Pascal's rule) and
/// `Nat.succ_sub_succ`.
///
/// **This is the content of the binomial theorem over ℂ** — the reindexing
/// identity that combines the two induction hypotheses the `a`-side and
/// `b`-side each reduce to. Two `Nat`-side substitutions
/// (`nat_eq_to_complex_equiv` on `choose_succ_succ`/`succ_sub_succ`) move
/// Pascal's rule and the exponent identity into a `Complex` context;
/// [`ComplexPrelude::of_nat_add`] turns the resulting `ofNat` of a `Nat` sum
/// into a genuine `Complex.add` of the two cast coefficients; and the rest —
/// distributing that sum through the two products, peeling one factor of `a`
/// off `pow a (succ k)` via [`ComplexPrelude::pow_succ`], and reassociating —
/// is decided by `ring_law_proof` over the five opaque atoms `ofNat (choose
/// n k)`, `ofNat (choose n (succ k))`, `a`, `pow a k`, `pow b (sub n k)`.
fn pascal_split_term_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    k: ExprId,
) -> ExprId {
    let sn = d.succ(n);
    let sk = d.succ(k);
    let lhs = binom_term_c(d, p, a, b, sn, sk);

    let nat_p = d.prelude();
    let c1 = d.choose(n, k);
    let c2 = d.choose(n, sk);
    let c_sn_sk = d.choose(sn, sk);
    let sum_c1c2 = NatOps::add(d, c1, c2);

    let ak_succ = d.const_app(p.pow, &[a, sk]);
    let sub_sn_sk = d.sub(sn, sk);
    let bpow_sn_sk = d.const_app(p.pow, &[b, sub_sn_sk]);

    // Step A: Pascal's rule on the Nat coefficient.
    let h_pascal_nat = d.lemma(nat_p.choose_succ_succ, &[n, k]); // Eq Nat(c_sn_sk, sum_c1c2)
    let h_a = nat_eq_to_complex_equiv(d, p, c_sn_sk, sum_c1c2, h_pascal_nat, &|d, c| {
        let of_c = d.const_app(p.of_nat, &[c]);
        let c_ak = d.const_app(p.mul, &[of_c, ak_succ]);
        d.const_app(p.mul, &[c_ak, bpow_sn_sk])
    });
    let of_sum = d.const_app(p.of_nat, &[sum_c1c2]);
    let c_ak_m1 = d.const_app(p.mul, &[of_sum, ak_succ]);
    let m1a = d.const_app(p.mul, &[c_ak_m1, bpow_sn_sk]);
    // h_a : Equiv(lhs, m1a)

    // Step B: succ_sub_succ on the Nat exponent.
    let sub_nk = d.sub(n, k);
    let h_sub_nat = d.lemma(nat_p.succ_sub_succ, &[n, k]); // Eq Nat(sub_sn_sk, sub_nk)
    let h_b = nat_eq_to_complex_equiv(d, p, sub_sn_sk, sub_nk, h_sub_nat, &|d, s| {
        let bpow = d.const_app(p.pow, &[b, s]);
        d.const_app(p.mul, &[c_ak_m1, bpow])
    });
    let bpow_nk = d.const_app(p.pow, &[b, sub_nk]);
    let m1 = d.const_app(p.mul, &[c_ak_m1, bpow_nk]);
    // h_b : Equiv(m1a, m1)

    // Step C: `of_nat_add` turns the `ofNat` of a `Nat` sum into a genuine
    // `Complex.add` of the two cast coefficients.
    let of_c1 = d.const_app(p.of_nat, &[c1]);
    let of_c2 = d.const_app(p.of_nat, &[c2]);
    let h_add = d.lemma(p.of_nat_add, &[c1, c2]); // Equiv(of_sum, add(of_c1,of_c2))
    let sum_c = d.const_app(p.add, &[of_c1, of_c2]);
    let refl_ak_succ = d.lemma(p.equiv_refl, &[ak_succ]);
    let h_c1 = d.lemma(
        p.mul_congr,
        &[of_sum, sum_c, ak_succ, ak_succ, h_add, refl_ak_succ],
    );
    let c_ak_m2 = d.const_app(p.mul, &[sum_c, ak_succ]);
    let refl_bpow_nk = d.lemma(p.equiv_refl, &[bpow_nk]);
    let h_c = d.lemma(
        p.mul_congr,
        &[c_ak_m1, c_ak_m2, bpow_nk, bpow_nk, h_c1, refl_bpow_nk],
    );
    let m2 = d.const_app(p.mul, &[c_ak_m2, bpow_nk]);
    // h_c : Equiv(m1, m2)

    // Step ring1: redistribute (C1+C2)*Aksucc*Bp into T1 + T2.
    let of_c1_v = CExpr::var(d, p, of_c1);
    let of_c2_v = CExpr::var(d, p, of_c2);
    let ak_succ_v = CExpr::var(d, p, ak_succ);
    let bpow_nk_v = CExpr::var(d, p, bpow_nk);
    let m2_c = CExpr::mul(
        CExpr::mul(
            CExpr::add(of_c1_v.clone(), of_c2_v.clone()),
            ak_succ_v.clone(),
        ),
        bpow_nk_v.clone(),
    );
    let t1_c = CExpr::mul(CExpr::mul(of_c1_v, ak_succ_v.clone()), bpow_nk_v.clone());
    let t2_c = CExpr::mul(CExpr::mul(of_c2_v, ak_succ_v), bpow_nk_v);
    let m2p_c = CExpr::add(t1_c.clone(), t2_c.clone());
    let h_ring1 = ring_law_proof(d, p, &m2_c, &m2p_c);
    let t1 = render_c(d, p, &t1_c);
    let t2 = render_c(d, p, &t2_c);
    let m2p = render_c(d, p, &m2p_c);
    // h_ring1 : Equiv(m2, m2p) where m2p = add(t1, t2)

    // Step D: `pow_succ` peels a factor of `a` off `pow a (succ k)`, inside
    // `t1` only — `t2` already matches `pascal_tail_term_c a b n k` exactly.
    let h_pow_succ_eq = d.lemma(p.pow_succ, &[a, k]); // Eq Complex(ak_succ, mul(ak,a))
    let ak = d.const_app(p.pow, &[a, k]);
    let ak_a = d.const_app(p.mul, &[ak, a]);
    let h_pow_succ = complex_eq_to_equiv(d, p, ak_succ, ak_a, h_pow_succ_eq);
    let refl_of_c1 = d.lemma(p.equiv_refl, &[of_c1]);
    let h_d1 = d.lemma(
        p.mul_congr,
        &[of_c1, of_c1, ak_succ, ak_a, refl_of_c1, h_pow_succ],
    );
    let c1_aka = d.const_app(p.mul, &[of_c1, ak_a]);
    let inner_t1 = d.const_app(p.mul, &[of_c1, ak_succ]);
    let refl_bpow_nk2 = d.lemma(p.equiv_refl, &[bpow_nk]);
    let h_d = d.lemma(
        p.mul_congr,
        &[inner_t1, c1_aka, bpow_nk, bpow_nk, h_d1, refl_bpow_nk2],
    );
    let t1p = d.const_app(p.mul, &[c1_aka, bpow_nk]);
    // h_d : Equiv(t1, t1p)

    // Step ring2: pull `a` out front — `(C1*(Ak*A))*Bp ~ A*((C1*Ak)*Bp)`.
    let of_c1_v2 = CExpr::var(d, p, of_c1);
    let ak_v = CExpr::var(d, p, ak);
    let a_v = CExpr::var(d, p, a);
    let bpow_nk_v2 = CExpr::var(d, p, bpow_nk);
    let t1p_c = CExpr::mul(
        CExpr::mul(of_c1_v2.clone(), CExpr::mul(ak_v.clone(), a_v.clone())),
        bpow_nk_v2.clone(),
    );
    let target2_c = CExpr::mul(a_v, CExpr::mul(CExpr::mul(of_c1_v2, ak_v), bpow_nk_v2));
    let h_ring2 = ring_law_proof(d, p, &t1p_c, &target2_c);
    let target2 = render_c(d, p, &target2_c);
    // h_ring2 : Equiv(t1p, target2) where target2 = mul(a, binom_term_c a b n k)

    let h_t1_to_target2 = d.lemma(p.equiv_trans, &[t1, t1p, target2, h_d, h_ring2]);

    let refl_t2 = d.lemma(p.equiv_refl, &[t2]);
    let h_final_add = d.lemma(
        p.add_congr,
        &[t1, target2, t2, t2, h_t1_to_target2, refl_t2],
    );
    let final_target = d.const_app(p.add, &[target2, t2]);

    let step1 = d.lemma(p.equiv_trans, &[lhs, m1a, m1, h_a, h_b]);
    let step2 = d.lemma(p.equiv_trans, &[lhs, m1, m2, step1, h_c]);
    let step3 = d.lemma(p.equiv_trans, &[lhs, m2, m2p, step2, h_ring1]);
    d.lemma(p.equiv_trans, &[lhs, m2p, final_target, step3, h_final_add])
}

/// `Equiv (binom_term_c a b row 0) (pow b row)` — the front boundary term of
/// any row's expansion, needed at `row = n` (the `b`-side) and `row = succ n`
/// (the final front-peel of `S(succ n)`), hence generalized over `row`.
///
/// `pow a Nat.zero` and `Nat.sub row Nat.zero` both ι-reduce away (to
/// `Complex.one` and `row` respectively), so this needs only
/// `nat_eq_to_complex_equiv` on the public `Nat.choose_zero_right` plus
/// `ring_law_proof` to collapse the resulting `ofNat 1` (itself
/// `Complex.add Complex.zero Complex.one` by one ι-step of
/// [`ComplexPrelude::of_nat`]) against the two multiplicative units.
fn binom_term_zero_eq_pow_b_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    row: ExprId,
) -> ExprId {
    let nat_p = d.prelude();
    let zero_n = d.zero();
    let start = binom_term_c(d, p, a, b, row, zero_n);

    let ak0 = d.const_app(p.pow, &[a, zero_n]);
    let c0 = d.choose(row, zero_n);
    let bpow_row = d.const_app(p.pow, &[b, row]);

    let h_c0_nat = d.lemma(nat_p.choose_zero_right, &[row]); // Eq Nat(c0, 1)
    let one_n = d.num(1);
    let h_lift = nat_eq_to_complex_equiv(d, p, c0, one_n, h_c0_nat, &|d, c| {
        let of_c = d.const_app(p.of_nat, &[c]);
        let c_ak0 = d.const_app(p.mul, &[of_c, ak0]);
        let sub_term = d.sub(row, zero_n);
        let bp = d.const_app(p.pow, &[b, sub_term]);
        d.const_app(p.mul, &[c_ak0, bp])
    });
    // h_lift : Equiv(start, mul(mul(ofNat 1, ak0), pow(b, sub(row,0))))

    let bp_v = CExpr::var(d, p, bpow_row);
    let mid_c = CExpr::mul(
        CExpr::mul(CExpr::add(CExpr::Zero, CExpr::One), CExpr::One),
        bp_v.clone(),
    );
    let target_c = bp_v;
    let h_ring = ring_law_proof(d, p, &mid_c, &target_c);
    let mid_term = render_c(d, p, &mid_c);

    d.lemma(p.equiv_trans, &[start, mid_term, bpow_row, h_lift, h_ring])
}

/// `Nat.lt k m → Eq Nat (Nat.sub m k) (Nat.succ (Nat.sub m (Nat.succ k)))` —
/// giving a truncated difference known positive a successor shape.
///
/// This is `nat_prelude::choose::sub_succ_of_lt`'s own construction (private
/// to that module, and `nat_prelude` is a live lane's directory), rebuilt
/// here from PUBLIC `Nat` prelude facts only — `le_dest` +
/// `add_sub_cancel_left` — exactly as that helper is, so nothing under
/// `nat_prelude/` is touched or duplicated as new prelude surface.
fn nat_sub_succ_of_lt(
    d: &mut IntDev<'_>,
    np: NatPrelude,
    m: ExprId,
    k: ExprId,
    hlt: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let sk = d.succ(k);

    let represented = d.lemma(np.le_dest, &[sk, m, hlt]);
    let predicate = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sum = NatOps::add(d, sk, j);
        let body = d.eq(sum, m);
        d.lam_fv(j_fv, nat, body)
    };

    let sub_mk = d.sub(m, k);
    let sub_m_sk = d.sub(m, sk);
    let target = {
        let s = d.succ(sub_m_sk);
        d.eq(sub_mk, s)
    };

    let minor = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sum = NatOps::add(d, sk, j);
        let e_ty = d.eq(sum, m);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        let kj = NatOps::add(d, k, j);
        let succ_kj = d.succ(kj);
        let sum_eq_succ_kj = d.lemma(np.succ_add, &[k, j]);
        let sym_e = d.symm(sum, m, e);
        let m_eq_succ_kj = d.trans(m, sum, succ_kj, sym_e, sum_eq_succ_kj);
        let succ_kj_eq_m = d.symm(m, succ_kj, m_eq_succ_kj);

        let cancel1 = d.lemma(np.add_sub_cancel_left, &[sk, j]);
        let sub_m_sk_eq_j = {
            let motive = d.eq_motive(sum, &|d, x| {
                let s = d.sub(x, sk);
                d.eq(s, j)
            });
            d.transport(sum, motive, cancel1, m, e)
        };

        let succ_j = d.succ(j);
        let k_succ_j = NatOps::add(d, k, succ_j);
        let cancel2 = d.lemma(np.add_sub_cancel_left, &[k, succ_j]);
        let sub_m_k_eq_succ_j = {
            let motive = d.eq_motive(k_succ_j, &|d, x| {
                let s = d.sub(x, k);
                d.eq(s, succ_j)
            });
            d.transport(k_succ_j, motive, cancel2, m, succ_kj_eq_m)
        };

        let congr_succ = d.congr(sub_m_sk, j, sub_m_sk_eq_j, &|d, x| d.succ(x));
        let succ_sub_m_sk = d.succ(sub_m_sk);
        let rev = d.symm(succ_sub_m_sk, succ_j, congr_succ);
        let final_ = d.trans(sub_mk, succ_j, succ_sub_m_sk, sub_m_k_eq_succ_j, rev);

        let with_e = d.lam_fv(e_fv, e_ty, final_);
        d.lam_fv(j_fv, nat, with_e)
    };

    exists_elim(d, predicate, target, represented, minor)
}

/// `Equiv (pascal_tail_term_c a b n k) (mul b (binom_term_c a b n (succ
/// k)))`, for `k < n` — needs [`nat_sub_succ_of_lt`] to give the `b`-exponent
/// a successor shape, which [`ComplexPrelude::pow_succ`] then peels into a
/// trailing `* b` matching the `b`-side's `mul_sum_range` reindex.
fn b_side_term_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    k: ExprId,
    hlt: ExprId,
) -> ExprId {
    let nat_p = d.prelude();
    let sk = d.succ(k);
    let start = pascal_tail_term_c(d, p, a, b, n, k);

    let c2 = d.choose(n, sk);
    let of_c2 = d.const_app(p.of_nat, &[c2]);
    let ak_succ = d.const_app(p.pow, &[a, sk]);
    let c_ak = d.const_app(p.mul, &[of_c2, ak_succ]);
    let sub_nk = d.sub(n, k);
    let sub_n_sk = d.sub(n, sk);

    let h_lt_nat = nat_sub_succ_of_lt(d, nat_p, n, k, hlt); // Eq Nat(sub_nk, succ(sub_n_sk))
    let succ_sub_n_sk = d.succ(sub_n_sk);
    let h1 = nat_eq_to_complex_equiv(d, p, sub_nk, succ_sub_n_sk, h_lt_nat, &|d, x| {
        let bp = d.const_app(p.pow, &[b, x]);
        d.const_app(p.mul, &[c_ak, bp])
    });
    let bpow_succ = d.const_app(p.pow, &[b, succ_sub_n_sk]);
    let mid1 = d.const_app(p.mul, &[c_ak, bpow_succ]);
    // h1 : Equiv(start, mid1)

    let bpow_n_sk = d.const_app(p.pow, &[b, sub_n_sk]);
    let bpow_n_sk_b = d.const_app(p.mul, &[bpow_n_sk, b]);
    let h_pow_succ_eq = d.lemma(p.pow_succ, &[b, sub_n_sk]); // Eq Complex(bpow_succ, bpow_n_sk_b)
    let h_pow_succ = complex_eq_to_equiv(d, p, bpow_succ, bpow_n_sk_b, h_pow_succ_eq);
    let refl_c_ak = d.lemma(p.equiv_refl, &[c_ak]);
    let h2 = d.lemma(
        p.mul_congr,
        &[c_ak, c_ak, bpow_succ, bpow_n_sk_b, refl_c_ak, h_pow_succ],
    );
    let mid2 = d.const_app(p.mul, &[c_ak, bpow_n_sk_b]);
    // h2 : Equiv(mid1, mid2)

    let c_ak_v = CExpr::var(d, p, c_ak);
    let bpow_n_sk_v = CExpr::var(d, p, bpow_n_sk);
    let b_v = CExpr::var(d, p, b);
    let lhs3_c = CExpr::mul(c_ak_v.clone(), CExpr::mul(bpow_n_sk_v.clone(), b_v.clone()));
    let rhs3_c = CExpr::mul(b_v, CExpr::mul(c_ak_v, bpow_n_sk_v));
    let h3 = ring_law_proof(d, p, &lhs3_c, &rhs3_c);
    let target = render_c(d, p, &rhs3_c);
    // h3 : Equiv(mid2, target) where target = mul(b, binom_term_c a b n (succ k))

    let t1 = d.lemma(p.equiv_trans, &[start, mid1, mid2, h1, h2]);
    d.lemma(p.equiv_trans, &[start, mid2, target, t1, h3])
}

/// The `a`-side of the induction step: reindex the front-peeled TAIL of
/// `S(succ n)`'s own sum through [`pascal_split_term_c`] via
/// [`ComplexPrelude::sum_range_congr`] (unconditional), then split the
/// resulting sum via [`ComplexPrelude::sum_range_add`] and collapse its first
/// half via [`ComplexPrelude::mul_sum_range`].
///
/// Proves `Equiv (sumRange (fun k => binom_term_c a b (succ n) (succ k))
/// (succ n)) (add (mul a (binom_sum_c a b n)) (sumRange (pascal_tail_fn_c a b
/// n) (succ n)))`.
fn a_side_lemma_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let sn = d.succ(n);
    let nat = d.nat_ty();

    let f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let body = binom_term_c(d, p, a, b, sn, sk);
        d.lam_fv(k_fv, nat, body)
    };

    let g = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let term_nk = binom_term_c(d, p, a, b, n, k);
        let a_term = d.const_app(p.mul, &[a, term_nk]);
        let tail = pascal_tail_term_c(d, p, a, b, n, k);
        let body = d.const_app(p.add, &[a_term, tail]);
        d.lam_fv(k_fv, nat, body)
    };

    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = pascal_split_term_c(d, p, a, b, n, i);
        d.lam_fv(i_fv, nat, body)
    };
    let h_congr = d.lemma(p.sum_range_congr, &[f, g, sn, pointwise]);
    // h_congr : Equiv(sumRange f sn, sumRange g sn)

    let f1 = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let term_nk = binom_term_c(d, p, a, b, n, k);
        let body = d.const_app(p.mul, &[a, term_nk]);
        d.lam_fv(k_fv, nat, body)
    };
    let g1 = pascal_tail_fn_c(d, p, a, b, n);
    let h_sra = d.lemma(p.sum_range_add, &[f1, g1, sn]);
    // h_sra : Equiv(sumRange g sn, add(sumRange f1 sn, sumRange g1 sn))

    let term_n_fn = binom_term_fn_c(d, p, a, b, n);
    let s_n = d.const_app(p.sum_range, &[term_n_fn, sn]);
    let h_msr = d.lemma(p.mul_sum_range, &[a, term_n_fn, sn]);
    // h_msr : Equiv(mul(a,s_n), sumRange f1 sn)
    let mul_a_sn = d.const_app(p.mul, &[a, s_n]);
    let sum_f1_sn = d.const_app(p.sum_range, &[f1, sn]);
    let h_msr_symm = d.lemma(p.equiv_symm, &[mul_a_sn, sum_f1_sn, h_msr]);

    let sum_g1_sn = d.const_app(p.sum_range, &[g1, sn]);
    let rhs_sra = d.const_app(p.add, &[sum_f1_sn, sum_g1_sn]);
    let final_target = d.const_app(p.add, &[mul_a_sn, sum_g1_sn]);
    let refl_sum_g1_sn = d.lemma(p.equiv_refl, &[sum_g1_sn]);
    let h_final = d.lemma(
        p.add_congr,
        &[
            sum_f1_sn,
            mul_a_sn,
            sum_g1_sn,
            sum_g1_sn,
            h_msr_symm,
            refl_sum_g1_sn,
        ],
    );

    let sum_f_sn = d.const_app(p.sum_range, &[f, sn]);
    let sum_g_sn = d.const_app(p.sum_range, &[g, sn]);
    let t1 = d.lemma(
        p.equiv_trans,
        &[sum_f_sn, sum_g_sn, rhs_sra, h_congr, h_sra],
    );
    d.lemma(
        p.equiv_trans,
        &[sum_f_sn, rhs_sra, final_target, t1, h_final],
    )
}

/// `Equiv (sumRange (pascal_tail_fn_c a b n) (succ n)) (sumRange
/// (pascal_tail_fn_c a b n) n)` — the tail sum's own boundary term (at `k =
/// n`) is `Equiv`-zero, since `choose n (succ n) = 0`
/// (`choose_succ_self_eq_zero`, public).
fn u_tail_boundary_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let nat_p = d.prelude();
    let u_fn = pascal_tail_fn_c(d, p, a, b, n);
    let sn = d.succ(n);
    let start = d.const_app(p.sum_range, &[u_fn, sn]);
    let sum_u_n = d.const_app(p.sum_range, &[u_fn, n]);
    let u_n = pascal_tail_term_c(d, p, a, b, n, n);

    let sn2 = d.succ(n);
    let c_n_sn = d.choose(n, sn2);
    let a_sn = d.const_app(p.pow, &[a, sn2]);
    let sub_nn = d.sub(n, n);
    let b_pow_nn = d.const_app(p.pow, &[b, sub_nn]);

    let h_czero_nat = d.lemma(nat_p.choose_succ_self_eq_zero, &[n]); // Eq Nat(c_n_sn, 0)
    let zero_n = d.zero();
    let h_lift = nat_eq_to_complex_equiv(d, p, c_n_sn, zero_n, h_czero_nat, &|d, c| {
        let of_c = d.const_app(p.of_nat, &[c]);
        let c_ak = d.const_app(p.mul, &[of_c, a_sn]);
        d.const_app(p.mul, &[c_ak, b_pow_nn])
    });
    // h_lift : Equiv(u_n, mul(mul(ofNat 0, a_sn), b_pow_nn))

    let a_sn_v = CExpr::var(d, p, a_sn);
    let b_pow_nn_v = CExpr::var(d, p, b_pow_nn);
    let mid_c = CExpr::mul(CExpr::mul(CExpr::Zero, a_sn_v), b_pow_nn_v);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let h_ring = ring_law_proof(d, p, &mid_c, &CExpr::Zero);
    let mid_term = render_c(d, p, &mid_c);
    // h_ring : Equiv(mid_term, zero_c)

    let u_zero = d.lemma(p.equiv_trans, &[u_n, mid_term, zero_c, h_lift, h_ring]);

    let refl_sum_u_n = d.lemma(p.equiv_refl, &[sum_u_n]);
    let h3 = d.lemma(
        p.add_congr,
        &[sum_u_n, sum_u_n, u_n, zero_c, refl_sum_u_n, u_zero],
    );
    let mid1 = d.const_app(p.add, &[sum_u_n, zero_c]);
    let h_az = d.lemma(p.add_zero, &[sum_u_n]);

    d.lemma(p.equiv_trans, &[start, mid1, sum_u_n, h3, h_az])
}

/// The `b`-side of the induction step: `Equiv (mul b (binom_sum_c a b n))
/// (add (pow b (succ n)) (sumRange (pascal_tail_fn_c a b n) n))`.
///
/// Front-peels `S(n)` itself ([`ComplexPrelude::sum_range_shift_front`]),
/// distributes `b` over the peeled front term and the tail sum
/// ([`ComplexPrelude::left_distrib`]), collapses `b * term_n(0) = b * pow(b,n)
/// = pow(b,succ n)` via [`binom_term_zero_eq_pow_b_c`], and reindexes the
/// tail via [`b_side_term_c`] under [`ComplexPrelude::sum_range_congr_lt`]
/// plus [`ComplexPrelude::mul_sum_range`].
fn b_side_lemma_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let sn = d.succ(n);
    let nat = d.nat_ty();
    let term_n_fn = binom_term_fn_c(d, p, a, b, n);
    let s_n = d.const_app(p.sum_range, &[term_n_fn, sn]);
    let start = d.const_app(p.mul, &[b, s_n]);

    let shifted_term_n_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let body = binom_term_c(d, p, a, b, n, sk);
        d.lam_fv(k_fv, nat, body)
    };
    let zero_n = d.zero();
    let term_n_0 = binom_term_c(d, p, a, b, n, zero_n);
    let tail_shifted_sum = d.const_app(p.sum_range, &[shifted_term_n_fn, n]);
    let h_shift = d.lemma(p.sum_range_shift_front, &[term_n_fn, n]);
    // h_shift : Equiv(s_n, add(term_n_0, tail_shifted_sum))
    let peeled = d.const_app(p.add, &[term_n_0, tail_shifted_sum]);
    let refl_b = d.lemma(p.equiv_refl, &[b]);
    let h1 = d.lemma(p.mul_congr, &[b, b, s_n, peeled, refl_b, h_shift]);
    let mid1 = d.const_app(p.mul, &[b, peeled]);

    let b_term_n0 = d.const_app(p.mul, &[b, term_n_0]);
    let b_tail_shifted = d.const_app(p.mul, &[b, tail_shifted_sum]);
    let distributed = d.const_app(p.add, &[b_term_n0, b_tail_shifted]);
    let h2 = d.lemma(p.left_distrib, &[b, term_n_0, tail_shifted_sum]);

    let pow_b_n = d.const_app(p.pow, &[b, n]);
    let h_bnd = binom_term_zero_eq_pow_b_c(d, p, a, b, n); // Equiv(term_n_0, pow_b_n)
    let b_pow_b_n = d.const_app(p.mul, &[b, pow_b_n]);
    let refl_b2 = d.lemma(p.equiv_refl, &[b]);
    let h3a = d.lemma(p.mul_congr, &[b, b, term_n_0, pow_b_n, refl_b2, h_bnd]);
    let pow_b_sn = d.const_app(p.pow, &[b, sn]);
    let h_comm = d.lemma(p.mul_comm, &[b, pow_b_n]); // Equiv(b_pow_b_n, mul(pow_b_n,b))
    let pow_b_n_b = d.const_app(p.mul, &[pow_b_n, b]);
    let h_pow_succ_eq = d.lemma(p.pow_succ, &[b, n]); // Eq Complex(pow_b_sn, pow_b_n_b)
    let h_pow_succ = complex_eq_to_equiv(d, p, pow_b_sn, pow_b_n_b, h_pow_succ_eq);
    let h3b = d.lemma(p.equiv_symm, &[pow_b_sn, pow_b_n_b, h_pow_succ]); // Equiv(pow_b_n_b, pow_b_sn)

    let t3a = d.lemma(
        p.equiv_trans,
        &[b_term_n0, b_pow_b_n, pow_b_n_b, h3a, h_comm],
    );
    let b_term_n0_chain = d.lemma(p.equiv_trans, &[b_term_n0, pow_b_n_b, pow_b_sn, t3a, h3b]);

    let mid2 = d.const_app(p.add, &[pow_b_sn, b_tail_shifted]);
    let refl_b_tail = d.lemma(p.equiv_refl, &[b_tail_shifted]);
    let h3 = d.lemma(
        p.add_congr,
        &[
            b_term_n0,
            pow_b_sn,
            b_tail_shifted,
            b_tail_shifted,
            b_term_n0_chain,
            refl_b_tail,
        ],
    );

    let u_fn = pascal_tail_fn_c(d, p, a, b, n);
    let sum_u_n = d.const_app(p.sum_range, &[u_fn, n]);

    let g_bounded = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let term_n_sk = binom_term_c(d, p, a, b, n, sk);
        let body = d.const_app(p.mul, &[b, term_n_sk]);
        d.lam_fv(k_fv, nat, body)
    };
    let pointwise_lt = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hlt_ty = d.lt(k, n);
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);
        let body = b_side_term_c(d, p, a, b, n, k, hlt);
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, body);
        d.lam_fv(k_fv, nat, with_hlt)
    };
    let h_congr_lt = d.lemma(p.sum_range_congr_lt, &[u_fn, g_bounded, n, pointwise_lt]);
    // h_congr_lt : Equiv(sum_u_n, sumRange g_bounded n)

    let h_msr = d.lemma(p.mul_sum_range, &[b, shifted_term_n_fn, n]);
    // h_msr : Equiv(b_tail_shifted, sumRange g_bounded n)
    let sum_g_bounded_n = d.const_app(p.sum_range, &[g_bounded, n]);
    let h_msr_via_congr_lt = d.lemma(p.equiv_symm, &[sum_u_n, sum_g_bounded_n, h_congr_lt]);
    let h4 = d.lemma(
        p.equiv_trans,
        &[
            b_tail_shifted,
            sum_g_bounded_n,
            sum_u_n,
            h_msr,
            h_msr_via_congr_lt,
        ],
    );

    let final_target = d.const_app(p.add, &[pow_b_sn, sum_u_n]);
    let refl_pow_b_sn = d.lemma(p.equiv_refl, &[pow_b_sn]);
    let h5 = d.lemma(
        p.add_congr,
        &[
            pow_b_sn,
            pow_b_sn,
            b_tail_shifted,
            sum_u_n,
            refl_pow_b_sn,
            h4,
        ],
    );

    let t1 = d.lemma(p.equiv_trans, &[start, mid1, distributed, h1, h2]);
    let t2 = d.lemma(p.equiv_trans, &[start, distributed, mid2, t1, h3]);
    d.lemma(p.equiv_trans, &[start, mid2, final_target, t2, h5])
}

/// The successor case of [`declare_add_pow`]'s induction: given `ih : Equiv
/// (pow (add a b) n) (binom_sum_c a b n)`, prove `Equiv (pow (add a b) (succ
/// n)) (binom_sum_c a b (succ n))`.
fn add_pow_step_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    ih: ExprId,
) -> ExprId {
    let sn = d.succ(n);
    let ab = d.const_app(p.add, &[a, b]);

    // LHS: `pow(ab, succ n)` ι-reduces to `mul(pow(ab,n), ab)` directly
    // (`Complex.pow`'s own defining equation), so the chain below starts from
    // `mul_pow_ab` with no explicit bridging step; the kernel accepts the
    // final proof against the stated goal (whose LHS is `pow(ab, succ n)`) by
    // defeq.
    let term_n_fn = binom_term_fn_c(d, p, a, b, n);
    let s_n = d.const_app(p.sum_range, &[term_n_fn, sn]);
    let pow_ab_n = d.const_app(p.pow, &[ab, n]);
    let mul_pow_ab = d.const_app(p.mul, &[pow_ab_n, ab]);

    let refl_ab = d.lemma(p.equiv_refl, &[ab]);
    let h_ih = d.lemma(p.mul_congr, &[pow_ab_n, s_n, ab, ab, ih, refl_ab]);
    let mul_sn_ab = d.const_app(p.mul, &[s_n, ab]);
    // h_ih : Equiv(mul_pow_ab, mul_sn_ab)

    let mul_sn_a = d.const_app(p.mul, &[s_n, a]);
    let mul_sn_b = d.const_app(p.mul, &[s_n, b]);
    let distributed = d.const_app(p.add, &[mul_sn_a, mul_sn_b]);
    let h_ld = d.lemma(p.left_distrib, &[s_n, a, b]);
    // h_ld : Equiv(mul_sn_ab, distributed)

    let mul_a_sn = d.const_app(p.mul, &[a, s_n]);
    let intermediate2 = d.const_app(p.add, &[mul_a_sn, mul_sn_b]);
    let h_comm_a = d.lemma(p.mul_comm, &[s_n, a]); // Equiv(mul_sn_a, mul_a_sn)
    let refl_mul_sn_b = d.lemma(p.equiv_refl, &[mul_sn_b]);
    let h_ca = d.lemma(
        p.add_congr,
        &[
            mul_sn_a,
            mul_a_sn,
            mul_sn_b,
            mul_sn_b,
            h_comm_a,
            refl_mul_sn_b,
        ],
    );
    // h_ca : Equiv(distributed, intermediate2)

    let mul_b_sn = d.const_app(p.mul, &[b, s_n]);
    let w = d.const_app(p.add, &[mul_a_sn, mul_b_sn]);
    let h_comm_b = d.lemma(p.mul_comm, &[s_n, b]); // Equiv(mul_sn_b, mul_b_sn)
    let refl_mul_a_sn = d.lemma(p.equiv_refl, &[mul_a_sn]);
    let h_cb = d.lemma(
        p.add_congr,
        &[
            mul_a_sn,
            mul_a_sn,
            mul_sn_b,
            mul_b_sn,
            refl_mul_a_sn,
            h_comm_b,
        ],
    );
    // h_cb : Equiv(intermediate2, w)

    let t_lhs1 = d.lemma(
        p.equiv_trans,
        &[mul_pow_ab, mul_sn_ab, distributed, h_ih, h_ld],
    );
    let t_lhs2 = d.lemma(
        p.equiv_trans,
        &[mul_pow_ab, distributed, intermediate2, t_lhs1, h_ca],
    );
    let lhs_to_w = d.lemma(p.equiv_trans, &[mul_pow_ab, intermediate2, w, t_lhs2, h_cb]);
    // lhs_to_w : Equiv(mul_pow_ab, w)

    // --- RHS: S(succ n) ------------------------------------------------
    let term_sn_fn = binom_term_fn_c(d, p, a, b, sn);
    let ssn = d.succ(sn);
    let s_sn = d.const_app(p.sum_range, &[term_sn_fn, ssn]);
    let zero_n = d.zero();
    let term_sn_0 = binom_term_c(d, p, a, b, sn, zero_n);
    let nat = d.nat_ty();
    let shifted_term_sn_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let body = binom_term_c(d, p, a, b, sn, sk);
        d.lam_fv(k_fv, nat, body)
    };
    let tail_sum = d.const_app(p.sum_range, &[shifted_term_sn_fn, sn]);
    let h_shift_sn = d.lemma(p.sum_range_shift_front, &[term_sn_fn, sn]);
    // h_shift_sn : Equiv(s_sn, add(term_sn_0, tail_sum))
    let peeled_sn = d.const_app(p.add, &[term_sn_0, tail_sum]);

    let pow_b_sn = d.const_app(p.pow, &[b, sn]);
    let h_bnd_sn = binom_term_zero_eq_pow_b_c(d, p, a, b, sn); // Equiv(term_sn_0, pow_b_sn)
    let refl_tail_sum = d.lemma(p.equiv_refl, &[tail_sum]);
    let h_r1 = d.lemma(
        p.add_congr,
        &[
            term_sn_0,
            pow_b_sn,
            tail_sum,
            tail_sum,
            h_bnd_sn,
            refl_tail_sum,
        ],
    );
    let mid_r1 = d.const_app(p.add, &[pow_b_sn, tail_sum]);
    // h_r1 : Equiv(peeled_sn, mid_r1)

    let u_fn = pascal_tail_fn_c(d, p, a, b, n);
    let sum_u_n_sn = d.const_app(p.sum_range, &[u_fn, sn]);
    let h_a_side = a_side_lemma_c(d, p, a, b, n);
    // h_a_side : Equiv(tail_sum, add(mul_a_sn, sum_u_n_sn))
    let split_tail = d.const_app(p.add, &[mul_a_sn, sum_u_n_sn]);
    let refl_pow_b_sn = d.lemma(p.equiv_refl, &[pow_b_sn]);
    let h_r2 = d.lemma(
        p.add_congr,
        &[
            pow_b_sn,
            pow_b_sn,
            tail_sum,
            split_tail,
            refl_pow_b_sn,
            h_a_side,
        ],
    );
    let mid_r2 = d.const_app(p.add, &[pow_b_sn, split_tail]);
    // h_r2 : Equiv(mid_r1, mid_r2)

    let pow_b_sn_v = CExpr::var(d, p, pow_b_sn);
    let mul_a_sn_v = CExpr::var(d, p, mul_a_sn);
    let sum_u_n_sn_v = CExpr::var(d, p, sum_u_n_sn);
    let lhs_lcomm_c = CExpr::add(
        pow_b_sn_v.clone(),
        CExpr::add(mul_a_sn_v.clone(), sum_u_n_sn_v.clone()),
    );
    let rhs_lcomm_c = CExpr::add(mul_a_sn_v, CExpr::add(pow_b_sn_v, sum_u_n_sn_v));
    let h_lcomm = ring_law_proof(d, p, &lhs_lcomm_c, &rhs_lcomm_c);
    let mid_r3 = render_c(d, p, &rhs_lcomm_c);
    // h_lcomm : Equiv(mid_r2, mid_r3)

    let pow_b_sn_plus_u = d.const_app(p.add, &[pow_b_sn, sum_u_n_sn]);
    let sum_u_n_n = d.const_app(p.sum_range, &[u_fn, n]);
    let h_u_bnd = u_tail_boundary_c(d, p, a, b, n); // Equiv(sum_u_n_sn, sum_u_n_n)
    let h_r3_inner = d.lemma(
        p.add_congr,
        &[
            pow_b_sn,
            pow_b_sn,
            sum_u_n_sn,
            sum_u_n_n,
            refl_pow_b_sn,
            h_u_bnd,
        ],
    );
    let b_sn_target = d.const_app(p.add, &[pow_b_sn, sum_u_n_n]);
    // h_r3_inner : Equiv(pow_b_sn_plus_u, b_sn_target)
    let refl_mul_a_sn2 = d.lemma(p.equiv_refl, &[mul_a_sn]);
    let h_r3 = d.lemma(
        p.add_congr,
        &[
            mul_a_sn,
            mul_a_sn,
            pow_b_sn_plus_u,
            b_sn_target,
            refl_mul_a_sn2,
            h_r3_inner,
        ],
    );
    let mid_r4 = d.const_app(p.add, &[mul_a_sn, b_sn_target]);
    // h_r3 : Equiv(mid_r3, mid_r4)

    let h_b_side = b_side_lemma_c(d, p, a, b, n);
    // h_b_side : Equiv(mul_b_sn, b_sn_target)
    let h_b_side_symm = d.lemma(p.equiv_symm, &[mul_b_sn, b_sn_target, h_b_side]);
    let refl_mul_a_sn3 = d.lemma(p.equiv_refl, &[mul_a_sn]);
    let h_r4 = d.lemma(
        p.add_congr,
        &[
            mul_a_sn,
            mul_a_sn,
            b_sn_target,
            mul_b_sn,
            refl_mul_a_sn3,
            h_b_side_symm,
        ],
    );
    // h_r4 : Equiv(mid_r4, w)

    let t_rhs1 = d.lemma(p.equiv_trans, &[s_sn, peeled_sn, mid_r1, h_shift_sn, h_r1]);
    let t_rhs2 = d.lemma(p.equiv_trans, &[s_sn, mid_r1, mid_r2, t_rhs1, h_r2]);
    let t_rhs3 = d.lemma(p.equiv_trans, &[s_sn, mid_r2, mid_r3, t_rhs2, h_lcomm]);
    let t_rhs4 = d.lemma(p.equiv_trans, &[s_sn, mid_r3, mid_r4, t_rhs3, h_r3]);
    let rhs_to_w = d.lemma(p.equiv_trans, &[s_sn, mid_r4, w, t_rhs4, h_r4]);
    // rhs_to_w : Equiv(s_sn, w)

    let w_to_rhs = d.lemma(p.equiv_symm, &[s_sn, w, rhs_to_w]);
    d.lemma(p.equiv_trans, &[mul_pow_ab, w, s_sn, lhs_to_w, w_to_rhs])
}

/// `Complex.add_pow` — the binomial theorem over ℂ, by induction on `n`.
///
/// The base case is a pure computation, decided by `ring_law_proof`
/// (`pow(ab,0)` and `binom_sum_c a b 0` both ι-reduce to expressions the ring
/// calculus normalizes to the same value: `Complex.one`). The successor case
/// is [`add_pow_step_c`].
fn declare_add_pow(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let ab = d.const_app(p.add, &[a, b]);
        let lhs = d.const_app(p.pow, &[ab, x]);
        let rhs = binom_sum_c(d, p, a, b, x);
        zeq(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            // `pow(ab,0)` ι-reduces to `one_c`; `binom_sum_c a b 0` ι-reduces
            // to `add(zero_c, mul(mul(ofNat(choose 0 0), pow(a,0)), pow(b,
            // sub(0,0))))`, and `choose 0 0`/`pow(a,0)`/`sub(0,0)`/`pow(b,0)`
            // are all GROUND `Nat`/`Complex.pow` computations that ι-reduce
            // fully regardless of `a`, `b`: `ofNat (choose 0 0)` collapses to
            // `add(zero_c,one_c)` (one ι-step of `ofNat` at the Nat literal
            // `1`).
            let lhs_c = CExpr::add(
                CExpr::Zero,
                CExpr::mul(
                    CExpr::mul(CExpr::add(CExpr::Zero, CExpr::One), CExpr::One),
                    CExpr::One,
                ),
            );
            ring_law_proof(d, p, &CExpr::One, &lhs_c)
        },
        &|d, j, ih| add_pow_step_c(d, p, a, b, j, ih),
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_b = d.pi_fv(b_fv, carrier, over_n);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_b = d.lam_fv(b_fv, carrier, over_n);
        d.lam_fv(a_fv, carrier, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.add_pow,
        uparams: vec![],
        ty,
        value,
    })
}

// --- roots of unity and the finite Fourier orthogonality relation ----------

/// `Complex.IsRootOfUnity z n := Equiv (pow z n) one`.
fn declare_is_root_of_unity(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pow_zn = d.const_app(p.pow, &[z, n]);
    let one = d.kernel().const_(p.one, vec![]);
    let body = zeq(d, p, pow_zn, one);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(z_fv, carrier, with_n)
    };
    let ty = {
        let inner = d.arrow(nat, prop);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_root_of_unity,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 10),
    })
}

/// `Complex.one_is_root_of_unity : ∀ n, IsRootOfUnity one n`.
fn declare_one_is_root_of_unity(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let one_c = d.kernel().const_(p.one, vec![]);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let pow_one_x = d.const_app(p.pow, &[one_c, x]);
        zeq(d, p, pow_one_x, one_c)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = d.const_app(p.is_root_of_unity, &[one_c, n]);

    let proof_inner = d.induct(
        &motive,
        &|d| d.lemma(p.equiv_refl, &[one_c]),
        &|d, j, ih| {
            let pow_one_j = d.const_app(p.pow, &[one_c, j]);
            let product = d.const_app(p.mul, &[pow_one_j, one_c]);
            let refl_one = d.lemma(p.equiv_refl, &[one_c]);
            let one_one = d.const_app(p.mul, &[one_c, one_c]);
            let step1 = d.lemma(p.mul_congr, &[pow_one_j, one_c, one_c, one_c, ih, refl_one]);
            let step2 = d.lemma(p.mul_one, &[one_c]); // Equiv (mul one one) one
            d.lemma(p.equiv_trans, &[product, one_one, one_c, step1, step2])
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt_inner);
    let value = d.lam_fv(n_fv, nat, proof_inner);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.one_is_root_of_unity,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.I_is_fourth_root : IsRootOfUnity I 4` — the negative control.
///
/// `pow I 4` is unfolded down to `mul (mul (mul (mul one I) I) I) I` purely by
/// iota-reduction (definitionally what [`ComplexPrelude::pow_succ`] applied
/// four times, plus [`ComplexPrelude::pow_zero`], assert), and the fully
/// expanded product is then decided by the ring calculus, which already
/// carries `I`'s components `(0, 1)` — the same fact
/// [`ComplexPrelude::i_sq`] states — so no separate appeal to `i_sq` as a
/// named lemma is needed on top of that.
fn declare_i_is_fourth_root(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let i_c = d.kernel().const_(p.i, vec![]);
    let four = d.num(4);
    let pow_i4 = d.const_app(p.pow, &[i_c, four]);

    let lhs_cexpr = CExpr::mul(
        CExpr::mul(
            CExpr::mul(CExpr::mul(CExpr::One, CExpr::I), CExpr::I),
            CExpr::I,
        ),
        CExpr::I,
    );
    let nested_term = render_c(d, p, &lhs_cexpr);
    let eq_fact = complex_eq_refl(d, p, nested_term);
    let equiv_fact = complex_eq_to_equiv(d, p, pow_i4, nested_term, eq_fact);
    let ring_fact = ring_law_proof(d, p, &lhs_cexpr, &CExpr::One);
    let one_term = render_c(d, p, &CExpr::One);
    let final_proof = d.lemma(
        p.equiv_trans,
        &[pow_i4, nested_term, one_term, equiv_fact, ring_fact],
    );

    let ty = d.const_app(p.is_root_of_unity, &[i_c, four]);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.i_is_fourth_root,
        uparams: vec![],
        ty,
        value: final_proof,
    })
}

/// `Complex.pow_mul : ∀ z (m n : Nat), Equiv (pow z (Nat.mul m n)) (pow (pow
/// z m) n)`.
fn declare_pow_mul(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let prod = NatOps::mul(d, m, x);
        let lhs = d.const_app(p.pow, &[z, prod]);
        let pow_z_m = d.const_app(p.pow, &[z, m]);
        let rhs = d.const_app(p.pow, &[pow_z_m, x]);
        zeq(d, p, lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let one = d.kernel().const_(p.one, vec![]);
            d.lemma(p.equiv_refl, &[one])
        },
        &|d, j, ih| {
            let mj = NatOps::mul(d, m, j);
            let pow_z_mj = d.const_app(p.pow, &[z, mj]);
            let sum = NatOps::add(d, mj, m);
            let start = d.const_app(p.pow, &[z, sum]);
            let pow_z_m = d.const_app(p.pow, &[z, m]);
            let after_pow_add = d.const_app(p.mul, &[pow_z_mj, pow_z_m]);
            let h_pow_add = d.lemma(p.pow_add, &[z, mj, m]);

            let pow_pzm_j = d.const_app(p.pow, &[pow_z_m, j]);
            let after_ih = d.const_app(p.mul, &[pow_pzm_j, pow_z_m]);
            let refl_pzm = d.lemma(p.equiv_refl, &[pow_z_m]);
            let h_ih = d.lemma(
                p.mul_congr,
                &[pow_z_mj, pow_pzm_j, pow_z_m, pow_z_m, ih, refl_pzm],
            );

            d.lemma(
                p.equiv_trans,
                &[start, after_pow_add, after_ih, h_pow_add, h_ih],
            )
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let inner2 = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(z_fv, carrier, inner2)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let inner2 = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(z_fv, carrier, inner2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_mul,
        uparams: vec![],
        ty,
        value,
    })
}

/// **The finite Fourier orthogonality relation.**
///
/// `Complex.geom_sum_eq_zero_of_root_of_unity : ∀ z n, IsRootOfUnity z n →
/// Apart (add one (neg z)) zero → Equiv (sumRange (fun k => pow z k) n)
/// zero`.
fn declare_geom_sum_eq_zero_of_root_of_unity(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let neg_z = d.const_app(p.neg, &[z]);
    let a = d.const_app(p.add, &[one_c, neg_z]); // a = 1 - z

    let pow_zn = d.const_app(p.pow, &[z, n]);
    let root_ty = d.const_app(p.is_root_of_unity, &[z, n]);
    let root_fv = d.fresh_fvar();
    let root_h = d.kernel().fvar(root_fv);

    let apart_ty = d.const_app(p.apart, &[a, zero_c]);
    let apart_fv = d.fresh_fvar();
    let apart_h = d.kernel().fvar(apart_fv);

    let pow_fn = |d: &mut IntDev<'_>| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = d.const_app(p.pow, &[z, i]);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };
    let f = pow_fn(d);
    let s = d.const_app(p.sum_range, &[f, n]); // s = sumRange (pow z .) n

    let target = zeq(d, p, s, zero_c); // Equiv s zero

    // --- h_mul_zero : Equiv (mul a s) zero ---------------------------------
    let h_geom = d.lemma(p.mul_sub_one_geom, &[z, n]);
    // h_geom : Equiv (mul a s) (add one (neg pow_zn))

    let neg_pow_zn = d.const_app(p.neg, &[pow_zn]);
    let rhs_geom = d.const_app(p.add, &[one_c, neg_pow_zn]);

    let neg_one = d.const_app(p.neg, &[one_c]);
    let add_one_neg_one = d.const_app(p.add, &[one_c, neg_one]);

    let neg_congr_root = d.lemma(p.neg_congr, &[pow_zn, one_c, root_h]);
    // neg_congr_root : Equiv (neg pow_zn) (neg one)
    let refl_one = d.lemma(p.equiv_refl, &[one_c]);
    let rhs_rewrite = d.lemma(
        p.add_congr,
        &[one_c, one_c, neg_pow_zn, neg_one, refl_one, neg_congr_root],
    );
    // rhs_rewrite : Equiv rhs_geom add_one_neg_one

    let add_neg_h = d.lemma(p.add_neg, &[one_c]); // Equiv add_one_neg_one zero
    let rhs_to_zero = d.lemma(
        p.equiv_trans,
        &[rhs_geom, add_one_neg_one, zero_c, rhs_rewrite, add_neg_h],
    );
    // rhs_to_zero : Equiv rhs_geom zero

    let mul_a_s = d.const_app(p.mul, &[a, s]);
    let h_mul_zero = d.lemma(
        p.equiv_trans,
        &[mul_a_s, rhs_geom, zero_c, h_geom, rhs_to_zero],
    );
    // h_mul_zero : Equiv (mul a s) zero

    // --- pos_a : CReal.lt CReal.zero (normSq a), from apart_h --------------
    let neg_zero_c = d.const_app(p.neg, &[zero_c]);
    let diff_a0 = d.const_app(p.add, &[a, neg_zero_c]);
    let norm_a0 = d.const_app(p.norm_sq, &[diff_a0]);
    let norm_a = d.const_app(p.norm_sq, &[a]);
    let creal_zero = czero(d, creal);
    let creal_zero_refl = crefl(d, creal, creal_zero);

    let shift_a = normsq_shift_zero_proof(d, p, a); // CReal.Equiv norm_a norm_a0
    let shift_a_symm = csymm(d, creal, norm_a, norm_a0, shift_a); // CReal.Equiv norm_a0 norm_a
    let pos_a = d.lemma(
        creal.lt_congr,
        &[
            creal_zero,
            creal_zero,
            norm_a0,
            norm_a,
            creal_zero_refl,
            shift_a_symm,
            apart_h,
        ],
    ); // CReal.lt zero norm_a

    // --- extract k, h : PosBound norm_a k -----------------------------------
    let k_fv = d.fresh_fvar();
    let k_var = d.kernel().fvar(k_fv);
    let pos_bound_template = d.const_app(creal.pos_bound, &[norm_a, k_var]);
    let predicate = d.lam_fv(k_fv, nat, pos_bound_template);
    let witness = d.const_app(creal.pos_bound_of_lt, &[norm_a, pos_a]);

    let minor = {
        let k2_fv = d.fresh_fvar();
        let k2 = d.kernel().fvar(k2_fv);
        let h_ty = d.const_app(creal.pos_bound, &[norm_a, k2]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let c = d.const_app(p.inv, &[a, k2, h]); // c = (1 - z)^-1
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        let c_zero = d.const_app(p.mul, &[c, zero_c]);
        let cong_h = d.lemma(p.mul_congr, &[c, c, mul_a_s, zero_c, refl_c, h_mul_zero]);
        // cong_h : Equiv (mul c (mul a s)) c_zero
        let c_as = d.const_app(p.mul, &[c, mul_a_s]);

        let c_a = d.const_app(p.mul, &[c, a]);
        let inv_mul_h = d.lemma(p.inv_mul_cancel, &[a, k2, h]); // Equiv c_a one
        let ca_s = d.const_app(p.mul, &[c_a, s]);
        let one_s = d.const_app(p.mul, &[one_c, s]);
        let refl_s = d.lemma(p.equiv_refl, &[s]);
        let step_b = d.lemma(p.mul_congr, &[c_a, one_c, s, s, inv_mul_h, refl_s]);
        // step_b : Equiv ca_s one_s

        let assoc = d.lemma(p.mul_assoc, &[c, a, s]); // Equiv ca_s c_as
        let assoc_symm = d.lemma(p.equiv_symm, &[ca_s, c_as, assoc]); // Equiv c_as ca_s
        let collapse = d.lemma(p.equiv_trans, &[c_as, ca_s, one_s, assoc_symm, step_b]);
        // collapse : Equiv c_as one_s

        let s_one = d.const_app(p.mul, &[s, one_c]);
        let comm_one_s = d.lemma(p.mul_comm, &[one_c, s]); // Equiv one_s s_one
        let mul_one_s = d.lemma(p.mul_one, &[s]); // Equiv s_one s
        let f_step = d.lemma(p.equiv_trans, &[one_s, s_one, s, comm_one_s, mul_one_s]);
        // f_step : Equiv one_s s

        let reduce = d.lemma(p.equiv_trans, &[c_as, one_s, s, collapse, f_step]);
        // reduce : Equiv c_as s
        let reduce_symm = d.lemma(p.equiv_symm, &[c_as, s, reduce]); // Equiv s c_as

        let step_final = d.lemma(p.equiv_trans, &[s, c_as, c_zero, reduce_symm, cong_h]);
        // step_final : Equiv s c_zero

        let mul_zero_c = d.lemma(p.mul_zero, &[c]); // Equiv c_zero zero
        let final_proof = d.lemma(p.equiv_trans, &[s, c_zero, zero_c, step_final, mul_zero_c]);
        // final_proof : Equiv s zero

        let with_h = d.lam_fv(h_fv, h_ty, final_proof);
        d.lam_fv(k2_fv, nat, with_h)
    };

    let final_result = exists_elim(d, predicate, target, witness, minor);

    let value = {
        let with_apart = d.lam_fv(apart_fv, apart_ty, final_result);
        let with_root = d.lam_fv(root_fv, root_ty, with_apart);
        let with_n = d.lam_fv(n_fv, nat, with_root);
        d.lam_fv(z_fv, carrier, with_n)
    };
    let ty = {
        let inner = d.arrow(apart_ty, target);
        let with_root = d.arrow(root_ty, inner);
        let with_n = d.pi_fv(n_fv, nat, with_root);
        d.pi_fv(z_fv, carrier, with_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_sum_eq_zero_of_root_of_unity,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (pow (mul z w) n) (mul (pow z n) (pow w n))` — not one of the
/// declared lemmas above; a private induction, needed only by
/// [`declare_root_of_unity_mul`].
fn complex_mul_pow(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    z: ExprId,
    w: ExprId,
    n: ExprId,
) -> ExprId {
    let mul_zw = d.const_app(p.mul, &[z, w]);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = d.const_app(p.pow, &[mul_zw, x]);
        let pow_z_x = d.const_app(p.pow, &[z, x]);
        let pow_w_x = d.const_app(p.pow, &[w, x]);
        let rhs = d.const_app(p.mul, &[pow_z_x, pow_w_x]);
        zeq(d, p, lhs, rhs)
    };

    d.induct(
        &motive,
        &|d| {
            let one_c = d.kernel().const_(p.one, vec![]);
            let mul_one_one = d.const_app(p.mul, &[one_c, one_c]);
            let h = d.lemma(p.mul_one, &[one_c]); // Equiv mul_one_one one_c
            d.lemma(p.equiv_symm, &[mul_one_one, one_c, h])
        },
        &|d, j, ih| {
            // ih : Equiv (pow mul_zw j) (mul (pow z j) (pow w j))
            let pow_mulzw_j = d.const_app(p.pow, &[mul_zw, j]);
            let start = d.const_app(p.mul, &[pow_mulzw_j, mul_zw]);

            let pow_z_j = d.const_app(p.pow, &[z, j]);
            let pow_w_j = d.const_app(p.pow, &[w, j]);
            let ih_applied = d.const_app(p.mul, &[pow_z_j, pow_w_j]);
            let refl_mulzw = d.lemma(p.equiv_refl, &[mul_zw]);
            let h_ih = d.lemma(
                p.mul_congr,
                &[pow_mulzw_j, ih_applied, mul_zw, mul_zw, ih, refl_mulzw],
            );
            let after_ih = d.const_app(p.mul, &[ih_applied, mul_zw]);
            // after_ih = mul (mul (pow z j) (pow w j)) (mul z w)

            let a_var = CExpr::var(d, p, pow_z_j);
            let b_var = CExpr::var(d, p, pow_w_j);
            let z_var = CExpr::var(d, p, z);
            let w_var = CExpr::var(d, p, w);
            let lhs_cexpr = CExpr::mul(
                CExpr::mul(a_var.clone(), b_var.clone()),
                CExpr::mul(z_var.clone(), w_var.clone()),
            );
            let rhs_cexpr = CExpr::mul(CExpr::mul(a_var, z_var), CExpr::mul(b_var, w_var));
            let target = render_c(d, p, &rhs_cexpr);
            // target = mul (mul (pow z j) z) (mul (pow w j) w)
            //        = mul (pow z (succ j)) (pow w (succ j))  -- definitionally
            let h_rearrange = ring_law_proof(d, p, &lhs_cexpr, &rhs_cexpr);

            d.lemma(p.equiv_trans, &[start, after_ih, target, h_ih, h_rearrange])
        },
        n,
    )
}

/// `Complex.root_of_unity_mul : ∀ z w n, IsRootOfUnity z n → IsRootOfUnity w
/// n → IsRootOfUnity (mul z w) n` — the `n`-th roots of unity are closed
/// under multiplication.
fn declare_root_of_unity_mul(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one_c = d.kernel().const_(p.one, vec![]);
    let pow_zn = d.const_app(p.pow, &[z, n]);
    let pow_wn = d.const_app(p.pow, &[w, n]);
    let root_z_ty = d.const_app(p.is_root_of_unity, &[z, n]);
    let root_w_ty = d.const_app(p.is_root_of_unity, &[w, n]);
    let root_z_fv = d.fresh_fvar();
    let root_z_h = d.kernel().fvar(root_z_fv);
    let root_w_fv = d.fresh_fvar();
    let root_w_h = d.kernel().fvar(root_w_fv);

    let mul_zw = d.const_app(p.mul, &[z, w]);
    let pow_mulzw_n = d.const_app(p.pow, &[mul_zw, n]);
    let target = d.const_app(p.is_root_of_unity, &[mul_zw, n]);

    let mul_pow_fact = complex_mul_pow(d, p, z, w, n);
    // mul_pow_fact : Equiv (pow (mul z w) n) (mul (pow z n) (pow w n))
    let ih_applied = d.const_app(p.mul, &[pow_zn, pow_wn]);

    let mul_one_one = d.const_app(p.mul, &[one_c, one_c]);
    let cong = d.lemma(
        p.mul_congr,
        &[pow_zn, one_c, pow_wn, one_c, root_z_h, root_w_h],
    ); // Equiv ih_applied mul_one_one

    let mul_one_h = d.lemma(p.mul_one, &[one_c]); // Equiv mul_one_one one_c

    let step1 = d.lemma(
        p.equiv_trans,
        &[pow_mulzw_n, ih_applied, mul_one_one, mul_pow_fact, cong],
    );
    let final_proof = d.lemma(
        p.equiv_trans,
        &[pow_mulzw_n, mul_one_one, one_c, step1, mul_one_h],
    );

    let value = {
        let with_w = d.lam_fv(root_w_fv, root_w_ty, final_proof);
        let with_z = d.lam_fv(root_z_fv, root_z_ty, with_w);
        let with_n = d.lam_fv(n_fv, nat, with_z);
        let with_ww = d.lam_fv(w_fv, carrier, with_n);
        d.lam_fv(z_fv, carrier, with_ww)
    };
    let ty = {
        let inner = d.arrow(root_w_ty, target);
        let with_z = d.arrow(root_z_ty, inner);
        let with_n = d.pi_fv(n_fv, nat, with_z);
        let with_w = d.pi_fv(w_fv, carrier, with_n);
        d.pi_fv(z_fv, carrier, with_w)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.root_of_unity_mul,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv a b → Equiv (pow a m) (pow b m)` — congruence of `pow` in its
/// *base* argument; not one of the declared lemmas above. Induction on `m`,
/// needed only by [`declare_root_of_unity_pow`].
fn complex_pow_congr(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    a: ExprId,
    b: ExprId,
    m: ExprId,
    h: ExprId,
) -> ExprId {
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let pow_a_x = d.const_app(p.pow, &[a, x]);
        let pow_b_x = d.const_app(p.pow, &[b, x]);
        zeq(d, p, pow_a_x, pow_b_x)
    };

    d.induct(
        &motive,
        &|d| {
            let one_c = d.kernel().const_(p.one, vec![]);
            d.lemma(p.equiv_refl, &[one_c])
        },
        &|d, j, ih| {
            let pow_a_j = d.const_app(p.pow, &[a, j]);
            let pow_b_j = d.const_app(p.pow, &[b, j]);
            d.lemma(p.mul_congr, &[pow_a_j, pow_b_j, a, b, ih, h])
        },
        m,
    )
}

/// `Complex.root_of_unity_pow : ∀ z m n, IsRootOfUnity z n → IsRootOfUnity
/// (pow z m) n` — the `n`-th roots of unity are closed under taking powers.
fn declare_root_of_unity_pow(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one_c = d.kernel().const_(p.one, vec![]);
    let pow_zn = d.const_app(p.pow, &[z, n]);
    let root_ty = d.const_app(p.is_root_of_unity, &[z, n]);
    let root_fv = d.fresh_fvar();
    let root_h = d.kernel().fvar(root_fv);

    let pow_zm = d.const_app(p.pow, &[z, m]);
    let pow_zm_n = d.const_app(p.pow, &[pow_zm, n]);
    let target = d.const_app(p.is_root_of_unity, &[pow_zm, n]);

    // step 1: Equiv (pow (pow z m) n) (pow z (mul m n))
    let mn = NatOps::mul(d, m, n);
    let pow_z_mn = d.const_app(p.pow, &[z, mn]);
    let pm1 = d.lemma(p.pow_mul, &[z, m, n]); // Equiv (pow z (mul m n)) (pow (pow z m) n)
    let step1 = d.lemma(p.equiv_symm, &[pow_z_mn, pow_zm_n, pm1]);
    // step1 : Equiv (pow (pow z m) n) (pow z (mul m n))

    // step 2: Equiv (pow z (mul m n)) (pow z (mul n m))
    let nm = NatOps::mul(d, n, m);
    let pow_z_nm = d.const_app(p.pow, &[z, nm]);
    let mul_comm_name = d.prelude().mul_comm;
    let h_comm = d.lemma(mul_comm_name, &[m, n]); // Eq Nat (mul m n) (mul n m)
    let step2 = nat_eq_to_complex_equiv(d, p, mn, nm, h_comm, &|d, x| d.const_app(p.pow, &[z, x]));
    // step2 : Equiv (pow z mn) (pow z nm)

    // step 3: Equiv (pow z (mul n m)) (pow (pow z n) m)
    let step3 = d.lemma(p.pow_mul, &[z, n, m]);

    // step 4: Equiv (pow (pow z n) m) (pow one m)
    let pow_zn_m = d.const_app(p.pow, &[pow_zn, m]);
    let pow_one_m = d.const_app(p.pow, &[one_c, m]);
    let step4 = complex_pow_congr(d, p, pow_zn, one_c, m, root_h);

    // step 5: Equiv (pow one m) one
    let step5 = d.lemma(p.one_is_root_of_unity, &[m]);

    let s12 = d.lemma(p.equiv_trans, &[pow_zm_n, pow_z_mn, pow_z_nm, step1, step2]);
    let s123 = d.lemma(p.equiv_trans, &[pow_zm_n, pow_z_nm, pow_zn_m, s12, step3]);
    let s1234 = d.lemma(p.equiv_trans, &[pow_zm_n, pow_zn_m, pow_one_m, s123, step4]);
    let final_proof = d.lemma(p.equiv_trans, &[pow_zm_n, pow_one_m, one_c, s1234, step5]);

    let value = {
        let with_root = d.lam_fv(root_fv, root_ty, final_proof);
        let with_n = d.lam_fv(n_fv, nat, with_root);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(z_fv, carrier, with_m)
    };
    let ty = {
        let inner = d.arrow(root_ty, target);
        let with_n = d.pi_fv(n_fv, nat, inner);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(z_fv, carrier, with_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.root_of_unity_pow,
        uparams: vec![],
        ty,
        value,
    })
}
