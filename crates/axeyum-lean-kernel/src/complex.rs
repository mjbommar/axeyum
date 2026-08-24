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
use crate::nat_prelude::NatOps;
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
    /// hypotheses give a positive norm ([`Self::apart_of_normSq_pos`]'s
    /// converse, inlined); `CReal.mul_pos` gives their product positive;
    /// [`Self::norm_sq_mul`] identifies that product with `normSq (mul z
    /// w)`; [`Self::apart_of_normSq_pos`]'s own bridging step closes it. See
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
        declare_mul_eq_zero_not_both_apart_zero(&mut d, prelude)
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
/// `normSq` is `CReal`-valued, so [`ring_law_proof`]'s `And.intro` of two
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
