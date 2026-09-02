//! **The least-upper-bound property's boundary certificate** (ADR-0603 row 2,
//! Spivak *Calculus* ch. 8 "Least Upper Bounds") — a machine-checked
//! reduction showing that a supremum for an arbitrary inhabited,
//! bounded-above set of reals decides an arbitrary proposition.
//!
//! ## What this file replaces
//!
//! `docs/curriculum/graded-statement-families.md` §2 recorded LUB's row 2 as
//! **pure absence**:
//!
//! > No function is exhibited whose classical supremum is not constructively
//! > computable … the unavailability is asserted, not proved.
//!
//! An asserted unavailability cannot fail, so it is not evidence — the same
//! defect [`CReal.evt_attained_max_decides_sign`](super::ExtremeValueNames::evt_attained_max_decides_sign)
//! (`creal/extreme_value.rs`) exists to remove for EVT, and
//! [`CReal.ivt_exact_root_decides_sign`](crate::IvtBoundaryNames::ivt_exact_root_decides_sign)
//! (`creal/ivt_boundary.rs`) for IVT. This file makes LUB's assertion a
//! theorem.
//!
//! ## The statement, and why this family
//!
//! Spivak's P13 says: **every inhabited set of reals that is bounded above
//! has a least upper bound.** It quantifies over an ARBITRARY set — not over
//! the range of a continuous function, not over a located set — so the
//! faithful counterexample family is a set carved out by an arbitrary
//! proposition:
//!
//! ```text
//! CReal.lubSet A := fun x => Or (le x zero) (And A (le x one))
//! ```
//!
//! that is, `(−∞, 0] ∪ ((−∞, 1] if A)`. Classically its supremum is `1` when
//! `A` holds and `0` when it does not, so **the supremum's own position
//! answers `A`** — the same move `evtLinear`'s maximiser makes for the sign
//! of `v`, one level more general because the question is now an arbitrary
//! `Prop` rather than a real comparison.
//!
//! Both of classical LUB's hypotheses are discharged as theorems here, so the
//! family is machine-checked to lie inside LUB's hypothesis class rather than
//! asserted to:
//!
//! - [`CReal.lubSet_inhabited`](super::LubBoundaryNames::lub_set_inhabited) —
//!   `∀ A, lubSet A zero`. Stated at the exhibited witness `0` rather than as
//!   `∃ x, lubSet A x`, which is strictly stronger and is what a constructive
//!   reading of "inhabited" demands (a *nonempty* set — one that is merely
//!   not empty — would be the classical reading and would weaken the result).
//! - [`CReal.lubSet_bounded`](super::LubBoundaryNames::lub_set_bounded) —
//!   `∀ A x, lubSet A x → le x one`. An explicit upper bound, again not an
//!   `∃`.
//!
//! ## What "has a supremum" is taken to mean, and why that reading is the
//! ## honest one
//!
//! The row-2 hypothesis is Bishop's definition of a supremum
//! (*Constructive Analysis*, ch. 2), not the classical one:
//!
//! ```text
//! (∀ x, lubSet A x → le x s)                                  -- s is an upper bound
//! (∀ t, lt t s → ∃ x, And (lubSet A x) (lt t x))              -- s is approached from within S
//! ```
//!
//! The second is the **approximation property**. It matters that this, and
//! not the classical "`s ≤ b` for every upper bound `b`", is what is assumed:
//!
//! - The classical leastness clause yields only `¬¬A` here (if `A` failed,
//!   `0` would be an upper bound, so `s ≤ 0`), and `¬¬A → A` is itself the
//!   decision principle at issue — the reduction would be circular.
//! - Bishop's clause is the one a *constructive* supremum is defined by, and
//!   it is exactly the clause `creal/sup_laws.rs`'s
//!   [`CReal.supOn_approx_lub`](super::CRealPrelude::sup_on_approx_lub)
//!   proves for the located case. So this row 2 refutes precisely the
//!   generalisation of row 1 that row 1 stops short of, rather than a
//!   strawman.
//!
//! The `∀ t < s` form is implied by Bishop's `ε`-form (`for each ε > 0 there
//! is `x ∈ S` with `x > s − ε`") — take `ε := s − t` — so assuming it assumes
//! no more than "S has a supremum in Bishop's sense".
//!
//! ## The conclusion is UNRESTRICTED EXCLUDED MIDDLE, which is a strictly
//! ## stronger boundary than IVT's and EVT's
//!
//! ```text
//! CReal.lub_decides_em : ∀ (A : Prop) (s : CReal),
//!   (∀ x, lubSet A x → le x s) →
//!   (∀ t, lt t s → Exists CReal (fun x => And (lubSet A x) (lt t x))) →
//!   Or A (Not A)
//! ```
//!
//! `evt_attained_max_decides_sign` and `ivt_exact_root_decides_sign` both
//! land on `∀ v, Or (le v zero) (le zero v)` — *analytic LLPO*, which is
//! consistent with Bishop's constructive mathematics. This lands on
//! `∀ A : Prop, Or A (Not A)`, which is not: it is the `em` that the logic
//! prelude's `em_of_dne` / `em_of_peirce` / `dne_of_em` / `peirce_of_em` take
//! as a *hypothesis* and never assert, and that this kernel deliberately does
//! not contain (`Decidable.em` exists and takes a `Decidable` instance;
//! ADR-0716 §2 measures the absence of the unrestricted form, with controls).
//!
//! So an *operator* handing back a supremum for every inhabited bounded set
//! would discharge the two hypotheses at every `A` at once and hand back
//! excluded middle for every proposition — including propositions about
//! `Nat`, which is why this boundary is not merely about the order on
//! `CReal` the way the other two are.
//!
//! ## The proof, on paper
//!
//! One [`CReal.lt_cotrans`](super::CRealPrelude::lt_cotrans) call on the
//! **fixed, always-strict** pair `zero < one`
//! ([`CReal.zero_lt_one`](super::CRealPrelude::zero_lt_one)) at `z := s` —
//! the same device both sibling row-2 proofs use, and for the same reason:
//! nothing anywhere decides an exact comparison. `lt_cotrans` returns
//! `Or (lt zero s) (lt s one)`, unconditionally.
//!
//! - **`0 < s`.** Instantiate the approximation hypothesis at `t := 0`. It
//!   returns an `x` with `lubSet A x` and `0 < x`. Split `lubSet A x`: the
//!   `x ≤ 0` disjunct contradicts `0 < x`
//!   (`lt_of_lt_of_le` then `lt_irrefl`), so the `And A (le x one)` disjunct
//!   holds and its left projection **is** `A`. Left disjunct.
//! - **`s < 1`.** Assume `A`. Then `1 ∈ S` by the right disjunct
//!   (`And.intro A (le_refl one)`), so the upper-bound hypothesis gives
//!   `1 ≤ s`; with `s < 1`, `lt_of_le_of_lt` gives `lt one one` and
//!   `lt_irrefl` closes it. That is `Not A`. Right disjunct.
//!
//! Note which instances are consumed: the upper-bound hypothesis at `x := 1`
//! only, the approximation hypothesis at `t := 0` only. They are stated in
//! full generality because LUB's own conclusion supplies them in full
//! generality — faithful hypotheses, not minimal ones, exactly as
//! `evt_attained_max_decides_sign` keeps its two unused interval hypotheses.
//! Weakening the statement to the two instances actually used would make the
//! theorem stronger and the *reduction* less recognisable as LUB; the
//! stronger form is available to anyone who wants it by instantiation.
//!
//! ## Honest scope — what this is NOT
//!
//! - This is **not** a proof that `∀ A : Prop, Or A (Not A)` is FALSE, and no
//!   such proof is available (excluded middle is consistent with this
//!   kernel's type theory — it is what a classical reading would simply
//!   assert). It is *unprovable here*, not refutable. What "refuted" means,
//!   precisely, is the same thing it means in `creal/extreme_value.rs`:
//!   **the classical conclusion is proved at least as strong as a decision
//!   principle this kernel demonstrably does not have.** It is falsifiable —
//!   land an unrestricted `em` and this stops being a refutation and becomes
//!   a route to LUB.
//! - This does **not** contradict
//!   [`CReal.supOn`](super::CRealPrelude::sup_on) and
//!   [`CReal.supOn_approx_lub`](super::CRealPrelude::sup_on_approx_lub)
//!   (`creal/supremum.rs`, `creal/sup_laws.rs`), LUB's row 1. Those construct
//!   the supremum of a **uniformly continuous function on a compact
//!   interval**, where the modulus itself supplies the locatedness a general
//!   set does not have. `lubSet A` is a set, not a function's range, and it
//!   is exactly as un-located as `A` is undecided — which is the whole
//!   content of the boundary.
//! - Nor does it contradict `creal/completeness.rs`'s **Bishop
//!   completeness** (`CReal.limit` of a `RegularSeq`), the other half of
//!   row 1: a regular sequence carries its own rate of convergence, and that
//!   rate is the data `lubSet A` lacks.

#![allow(clippy::doc_markdown)]

use super::convergence::{exists_elim, exists_ty};
use super::{CRealPrelude, and_intro, cle, clt, creal_ty};
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// Admit `CReal.lubSet`, its two hypothesis-class lemmas, and
/// `CReal.lub_decides_em`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_lub_boundary(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_lub_set(d, p)?;
    declare_lub_set_inhabited(d, p)?;
    declare_lub_set_bounded(d, p)?;
    declare_lub_decides_em(d, p)
}

// --- local term helpers -----------------------------------------------------

/// `CReal.lubSet a x`.
fn lub_set_at(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, x: ExprId) -> ExprId {
    d.const_app(p.lub_boundary.lub_set, &[a, x])
}

/// The two disjuncts `lubSet a x` unfolds to: `(le x zero, And a (le x one))`.
fn lub_set_disjuncts(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    x: ExprId,
) -> (ExprId, ExprId) {
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let below = cle(d, p, x, zero);
    let inside = cle(d, p, x, one);
    let raised = d.and(a, inside);
    (below, raised)
}

/// `le zero one`, from [`CRealPrelude::zero_lt_one`] through
/// [`CRealPrelude::le_of_lt`].
fn zero_le_one(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let strict = d.kernel().const_(p.zero_lt_one, vec![]);
    d.lemma(p.le_of_lt, &[zero, one, strict])
}

/// `False`, from a `lt x x` witness: [`CRealPrelude::lt_irrefl`] applied.
fn refute_lt_self(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, bad: ExprId) -> ExprId {
    let irrefl = d.lemma(p.lt_irrefl, &[x]);
    d.apply(irrefl, &[bad])
}

// --- `CReal.lubSet` ---------------------------------------------------------

/// `CReal.lubSet : Prop → CReal → Prop :=`
/// `fun A x => Or (le x zero) (And A (le x one))`.
///
/// The LUB counterexample family, as a named object so the row-2 statement,
/// its two hypothesis-class lemmas, and the tests can all refer to one thing.
/// Inhabited at `0`, bounded above by `1`, and *located only as far as `A` is
/// decided* — which is the entire point.
fn declare_lub_set(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let prop = d.kernel().sort_zero();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let (below, raised) = lub_set_disjuncts(d, p, a, x);
    let body = d.or(below, raised);
    let value = {
        let inner = d.lam_fv(x_fv, carrier, body);
        d.lam_fv(a_fv, prop, inner)
    };
    let ty = {
        let inner = d.arrow(carrier, prop);
        d.arrow(prop, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.lub_boundary.lub_set,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 1),
    })
}

// --- `CReal.lubSet_inhabited` -----------------------------------------------

/// `CReal.lubSet_inhabited : ∀ (A : Prop), lubSet A zero` — classical LUB's
/// first hypothesis, at an EXHIBITED witness rather than as an `∃`.
fn declare_lub_set_inhabited(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let prop = d.kernel().sort_zero();
    let zero = d.kernel().const_(p.zero, vec![]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let (below, raised) = lub_set_disjuncts(d, p, a, zero);
    let refl_zero = d.lemma(p.le_refl, &[zero]);
    let member = d.or_inl(below, raised, refl_zero);

    let claim = lub_set_at(d, p, a, zero);
    let ty = d.pi_fv(a_fv, prop, claim);
    let value = d.lam_fv(a_fv, prop, member);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.lub_boundary.lub_set_inhabited,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.lubSet_bounded` -------------------------------------------------

/// `CReal.lubSet_bounded : ∀ (A : Prop) (x : CReal), lubSet A x → le x one` —
/// classical LUB's second hypothesis, at an EXPLICIT bound rather than as an
/// `∃`. Both disjuncts land on `1`: the left through
/// [`CRealPrelude::le_trans`] against `0 ≤ 1`, the right by projection.
fn declare_lub_set_bounded(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let prop = d.kernel().sort_zero();
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let (below, raised) = lub_set_disjuncts(d, p, a, x);
    let hypothesis_ty = lub_set_at(d, p, a, x);
    let target = cle(d, p, x, one);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let body = d.or_elim(
        below,
        raised,
        target,
        h,
        &|d, hle| {
            let bridge = zero_le_one(d, p);
            d.lemma(p.le_trans, &[x, zero, one, hle, bridge])
        },
        &|d, hand| {
            let inside = cle(d, p, x, one);
            d.and_right(a, inside, hand)
        },
    );

    let ty = {
        let inner = d.arrow(hypothesis_ty, target);
        let with_x = d.pi_fv(x_fv, carrier, inner);
        d.pi_fv(a_fv, prop, with_x)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis_ty, body);
        let with_x = d.lam_fv(x_fv, carrier, with_h);
        d.lam_fv(a_fv, prop, with_x)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.lub_boundary.lub_set_bounded,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.lub_decides_em` -------------------------------------------------

/// `∀ x, lubSet a x → le x s`, the upper-bound half of "s is a supremum".
fn upper_bound_ty(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, s: ExprId) -> ExprId {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let member = lub_set_at(d, p, a, x);
    let bound = cle(d, p, x, s);
    let inner = d.arrow(member, bound);
    d.pi_fv(x_fv, carrier, inner)
}

/// `fun x => And (lubSet a x) (lt t x)` — the predicate the approximation
/// hypothesis produces a witness for.
fn approach_predicate(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, t: ExprId) -> ExprId {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let member = lub_set_at(d, p, a, x);
    let strict = clt(d, p, t, x);
    let body = d.and(member, strict);
    d.lam_fv(x_fv, carrier, body)
}

/// `∀ t, lt t s → Exists CReal (fun x => And (lubSet a x) (lt t x))` —
/// Bishop's approximation half of "s is a supremum".
fn approximation_ty(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, s: ExprId) -> ExprId {
    let carrier = creal_ty(d, p);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let below = clt(d, p, t, s);
    let predicate = approach_predicate(d, p, a, t);
    let witness_ty = exists_ty(d, p, carrier, predicate);
    let inner = d.arrow(below, witness_ty);
    d.pi_fv(t_fv, carrier, inner)
}

/// `CReal.lub_decides_em : ∀ (A : Prop) (s : CReal),`
/// `(∀ x, lubSet A x → le x s) →`
/// `(∀ t, lt t s → Exists CReal (fun x => And (lubSet A x) (lt t x))) →`
/// `Or A (Not A)` — this file's module documentation has the statement, the
/// reason for this particular family, and the two-branch paper proof.
fn declare_lub_decides_em(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let prop = d.kernel().sort_zero();
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);

    let hub_ty = upper_bound_ty(d, p, a, s);
    let happrox_ty = approximation_ty(d, p, a, s);

    let not_a = d.not(a);
    let target = d.or(a, not_a);

    let hub_fv = d.fresh_fvar();
    let hub = d.kernel().fvar(hub_fv);
    let happrox_fv = d.fresh_fvar();
    let happrox = d.kernel().fvar(happrox_fv);

    let lt_zero_s = clt(d, p, zero, s);
    let lt_s_one = clt(d, p, s, one);
    let strict = d.kernel().const_(p.zero_lt_one, vec![]);
    let cotrans = d.lemma(p.lt_cotrans, &[zero, one, strict, s]);

    let body = d.or_elim(
        lt_zero_s,
        lt_s_one,
        target,
        cotrans,
        // --- branch A: 0 < s  =>  A ----------------------------------------
        &|d, hpos| {
            let predicate = approach_predicate(d, p, a, zero);
            let witness = d.apply(happrox, &[zero, hpos]);
            let minor = {
                let x_fv = d.fresh_fvar();
                let x = d.kernel().fvar(x_fv);
                let member = lub_set_at(d, p, a, x);
                let above = clt(d, p, zero, x);
                let pair_ty = d.and(member, above);

                let hx_fv = d.fresh_fvar();
                let hx = d.kernel().fvar(hx_fv);
                let hmem = d.and_left(member, above, hx);
                let hlt = d.and_right(member, above, hx);

                let (below, raised) = lub_set_disjuncts(d, p, a, x);
                let split = d.or_elim(
                    below,
                    raised,
                    target,
                    hmem,
                    // x ≤ 0 contradicts 0 < x.
                    &|d, hle| {
                        let bad = d.lemma(p.lt_of_lt_of_le, &[zero, x, zero, hlt, hle]);
                        let false_proof = refute_lt_self(d, p, zero, bad);
                        d.absurd(target, false_proof)
                    },
                    // The other disjunct's left projection IS `A`.
                    &|d, hand| {
                        let inside = cle(d, p, x, one);
                        let ha = d.and_left(a, inside, hand);
                        d.or_inl(a, not_a, ha)
                    },
                );

                let with_hx = d.lam_fv(hx_fv, pair_ty, split);
                d.lam_fv(x_fv, carrier, with_hx)
            };
            exists_elim(d, p, carrier, predicate, target, witness, minor)
        },
        // --- branch B: s < 1  =>  ¬A ---------------------------------------
        &|d, hlt1| {
            let refutation = {
                let ha_fv = d.fresh_fvar();
                let ha = d.kernel().fvar(ha_fv);
                let (below, raised) = lub_set_disjuncts(d, p, a, one);
                let inside = cle(d, p, one, one);
                let refl_one = d.lemma(p.le_refl, &[one]);
                let pair = and_intro(d, p, a, inside, ha, refl_one);
                let member = d.or_inr(below, raised, pair);
                let one_le_s = d.apply(hub, &[one, member]);
                let bad = d.lemma(p.lt_of_le_of_lt, &[one, s, one, one_le_s, hlt1]);
                let false_proof = refute_lt_self(d, p, one, bad);
                d.lam_fv(ha_fv, a, false_proof)
            };
            d.or_inr(a, not_a, refutation)
        },
    );

    let ty = {
        let inner = d.arrow(happrox_ty, target);
        let with_hub = d.arrow(hub_ty, inner);
        let with_s = d.pi_fv(s_fv, carrier, with_hub);
        d.pi_fv(a_fv, prop, with_s)
    };
    let value = {
        let with_happrox = d.lam_fv(happrox_fv, happrox_ty, body);
        let with_hub = d.lam_fv(hub_fv, hub_ty, with_happrox);
        let with_s = d.lam_fv(s_fv, carrier, with_hub);
        d.lam_fv(a_fv, prop, with_s)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.lub_boundary.lub_decides_em,
        uparams: vec![],
        ty,
        value,
    })
}

/// The kernel names `creal/lub_boundary.rs` declares.
///
/// One of ADR-1512's per-module registries behind the [`CRealPrelude`]
/// facade: the field, its documentation and its interning all live
/// beside the `declare_*` that uses them, so a declaration added here
/// does not touch `creal.rs` at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LubBoundaryNames {
    /// `CReal.lubSet : Prop -> CReal -> Prop := fun A x => Or (le x zero)
    /// (And A (le x one))` -- the LUB counterexample family
    /// (`creal/lub_boundary.rs`), the set `(-inf, 0] union ((-inf, 1] if A)`.
    /// Classical supremum `1` when `A` holds and `0` when it does not, so
    /// *where the supremum sits* IS the truth value of `A`.
    ///
    /// Spivak ch. 8's P13 quantifies over an ARBITRARY inhabited bounded-above
    /// set, so a set carved out by an arbitrary `Prop` is faithful to the
    /// classical statement rather than a strawman -- and it is exactly the
    /// generalisation [`super::CRealPrelude::sup_on`] (a uniformly continuous function on a
    /// compact interval, whose modulus supplies the locatedness) stops short
    /// of.
    pub lub_set: NameId,
    /// `CReal.lubSet_inhabited : forall (A : Prop), lubSet A zero` -- classical
    /// LUB's first hypothesis, **proved rather than asserted**, and at an
    /// EXHIBITED witness rather than as an `Exists`. One [`super::CRealPrelude::le_refl`]
    /// under `Or.inl`. See `creal/lub_boundary.rs`.
    pub lub_set_inhabited: NameId,
    /// `CReal.lubSet_bounded : forall (A : Prop) (x : CReal), lubSet A x ->
    /// le x one` -- classical LUB's second hypothesis, **proved rather than
    /// asserted**, and at an EXPLICIT bound rather than as an `Exists`. The
    /// `x <= 0` disjunct reaches `1` through [`super::CRealPrelude::le_trans`] against
    /// `0 <= 1`, the other by projection. See `creal/lub_boundary.rs`.
    pub lub_set_bounded: NameId,
    /// `CReal.lub_decides_em : forall (A : Prop) (s : CReal),
    /// (forall x, lubSet A x -> le x s) ->
    /// (forall t, lt t s -> Exists CReal (fun x => And (lubSet A x) (lt t x)))
    /// -> Or A (Not A)` --
    /// **ADR-0603 row 2 for the least upper bound property**, machine-checked
    /// rather than asserted (`creal/lub_boundary.rs`).
    ///
    /// A supremum for [`super::LubBoundaryNames::lub_set`] -- in **Bishop's** sense, an upper
    /// bound plus the approximation property, which is the constructive
    /// definition and the one [`super::CRealPrelude::sup_on_approx_lub`] proves for the
    /// located case -- yields `Or A (Not A)` for an ARBITRARY proposition.
    /// That is UNRESTRICTED EXCLUDED MIDDLE, a strictly stronger boundary
    /// than [`super::ExtremeValueNames::evt_attained_max_decides_sign`] and
    /// [`crate::IvtBoundaryNames::ivt_exact_root_decides_sign`], which both land on analytic
    /// LLPO (consistent with Bishop; this is not).
    ///
    /// One [`super::CRealPrelude::lt_cotrans`] call on the fixed strict pair
    /// [`super::CRealPrelude::zero_lt_one`] at `z := s`: the `0 < s` branch reads `A` off the
    /// approximation witness at `t := 0`, and the `s < 1` branch refutes `A`
    /// because `A` would put `1` in the set. See that module's own
    /// documentation, including its "Honest scope" section: this proves the
    /// classical conclusion at least as strong as a decision principle this
    /// kernel does not have, NOT that the principle is false.
    pub lub_decides_em: NameId,
}

impl LubBoundaryNames {
    /// Interns this module's names under the `CReal` root.
    ///
    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel
    /// spelling of each name sits in the file that declares it.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            lub_set: kernel.name_str(creal, "lubSet"),
            lub_set_inhabited: kernel.name_str(creal, "lubSet_inhabited"),
            lub_set_bounded: kernel.name_str(creal, "lubSet_bounded"),
            lub_decides_em: kernel.name_str(creal, "lub_decides_em"),
        }
    }
}
