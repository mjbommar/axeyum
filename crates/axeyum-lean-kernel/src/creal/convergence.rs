//! **Convergence of sequences of `CReal`, and the first theorems of
//! analysis over our own reals** (ADR-0512, continuing phase R8).
//!
//! ## What `completeness.rs` already supplies, and why this module does not
//! reuse its shape verbatim
//!
//! [`CReal.RegularSeq`](super::CompletenessNames::regular_seq) and
//! [`CReal.limit_dist`](super::CompletenessNames::limit_dist) already contain a
//! notion of "converges": `limit_dist` proves, for `X`'s own Bishop limit,
//! `Within (seq (X n) k − seq (limit X h) k) (2/(k+1) + 2/(n+1))` — a rate
//! statement uniform in the *second* sampling index `k`. That shape is
//! specialised to the diagonal construction (it quantifies over the
//! representative index `k` at which the limit is *read*, not just at which
//! `X n` is *produced*) and is not a predicate relating an arbitrary
//! `f : Nat → CReal` to an arbitrary `L : CReal`. This module builds that
//! general predicate, in the same canonical-sample idiom
//! [`CReal.RegularSeq`](super::CompletenessNames::regular_seq) already uses (compare
//! `f n` against `L` at `f n`'s *own* index `n`, never through an arbitrary
//! third index), and reduces to `limit_dist`'s shape when `f` and `L` are
//! `X` and its own limit.
//!
//! ## `CReal.Converges`, and why it carries the modulus as a free constant
//!
//! ```text
//! CReal.Converges (f : Nat → CReal) (L : CReal) : Prop :=
//!   ∃ (K : Nat), ∀ (n : Nat), Within (seq (f n) n − seq L n) (Rat.natDivSucc K n)
//! ```
//!
//! The task brief's own suggested form is the textbook `∀ k, ∃ N, ∀ n ≥ N,
//! |f n − L| ≤ 1/(k+1)`. That form was tried first and abandoned: closing
//! [`converges_unique`] from it requires relating `CReal.le`/`CReal.add` at
//! the *representative* level across an index `N` that depends on `k` in no
//! controlled way, which is exactly the situation
//! [`Rat.natDivSucc_scale`](crate::RatPrelude::nat_div_succ_scale)'s own
//! documentation flags as needing an antitonicity-in-the-index lemma for
//! `Rat.natDivSucc` that this development deliberately never proves (every
//! existing estimate here is engineered to avoid it — see that lemma's own
//! comment and [`super::completeness`]'s "no arbitrary third index" remarks).
//! The definition above sidesteps the problem entirely: both hypotheses of
//! [`converges_unique`] are already stated at the *same* index `n`, so no
//! comparison across denominators is ever needed, and the whole proof is
//! elementary — one instance of
//! [`CReal.equiv_of_bounded`](super::CRealPrelude::equiv_of_bounded), the
//! `O(1/n)`-with-a-free-constant principle every asymptotic argument in this
//! development already runs on. This is the judgement call the task brief
//! explicitly allows ("prefer a modulus-carrying form if that is what the
//! existing development uses").
//!
//! This is a **faithful** notion of convergence, not a weakened stand-in for
//! one: `seq (f n) n` differs from the real `f n` itself by at most
//! `1/(n+1)` (regularity), so bounding `|seq (f n) n − seq L n| = O(1/n)` and
//! bounding `f n`'s full representative-independent distance to `L` by
//! `O(1/n)` are the same condition up to an additive constant that
//! `equiv_of_bounded`-style reasoning never cares about — exactly the reading
//! [`CReal.RegularSeq`](super::CompletenessNames::regular_seq)'s own module
//! documentation gives for the identical move.
//!
//! ## `CReal.Cauchy`, and the shape [`converges_cauchy`] needs
//!
//! ```text
//! CReal.Cauchy (f : Nat → CReal) : Prop :=
//!   ∃ (K : Nat), ∀ (m n : Nat),
//!     Within (seq (f m) m − seq (f n) n) (Rat.natDivSucc K m + Rat.natDivSucc K n)
//! ```
//!
//! the natural two-index generalisation of
//! [`CReal.RegularSeq`](super::CompletenessNames::regular_seq) to an unscaled
//! modulus. [`converges_cauchy`] combines `Converges f L`'s bound at `m` and
//! at `n` with `L`'s own regularity between `m` and `n`
//! ([`CReal.regular`](super::CRealPrelude::regular)) — three quantities, not
//! two, which is the one place this module's estimates need a genuine
//! four-term rearrangement ([`regroup_middle_four`]) rather than a single
//! `Rat.bounds_add`.
//!
//! ## The algebra of limits, and the shift bridge it needed
//!
//! [`declare_converges_add`] proves `Converges f L → Converges g M →
//! Converges (fun n => add (f n) (g n)) (add L M)`. `CReal.add`'s
//! representative samples at Bishop's shift `2n+1`, not at `n`
//! ([`CReal.add`](super::CRealPrelude::add)'s own documentation), so
//! `seq (add (f n) (g n)) n` is `seq (f n) (shift n) + seq (g n) (shift n)` —
//! **not** `seq (f n) n + seq (g n) n`, the quantity [`CReal.Converges`]
//! actually bounds. The blocker the previous slice reported was exactly this
//! bridge: relating a real's sample at `n` to its sample at `shift n` needs
//! [`half_shift_le`](super::completeness::half_shift_le)-shaped reasoning,
//! which was `fn`-private to [`super::completeness`] (Rust privacy: visible
//! in its defining module and that module's descendants only —
//! `creal::completeness` and `creal::convergence` are *siblings*, both
//! children of `creal`, so neither saw the other's private helpers).
//!
//! **Widening `half_shift_le` to `pub(super)` was sufficient — no
//! re-derivation was needed.** [`shift_regular_bound`] reuses it directly:
//! one instance of [`CReal.regular`](super::CRealPrelude::regular) at
//! `(x, shift n, n)` gives `Within (seq x (shift n) − seq x n) (modulus
//! (shift n) n)`, and `half_shift_le n` (plus `Rat.le_refl` and one
//! `Rat.natDivSucc_add` fusion) widens the bound to the flat `natDivSucc 2 n`
//! — cheap because [`super::completeness::convergence_bound_le`]-style
//! two-hop widening is not needed here: unlike `limit_dist`'s bridge (which
//! crosses *two* different sequences, `X n` and `X (shift k)`, at two
//! different indices), this bridge is a single real against *itself* at two
//! indices, so one `half_shift_le` instance closes it.
//!
//! [`declare_converges_add`]'s per-`n` estimate telescopes three terms with
//! the *same* denominator `n+1` — `seq (f n) (shift n) − seq (f n) n`
//! (`shift_regular_bound`, cost `2/(n+1)`), `seq (f n) n − seq L n`
//! (`Converges f L`'s own bound, cost `K₁/(n+1)`), and `seq L n − seq L
//! (shift n)` (`shift_regular_bound` again, negated, cost `2/(n+1)`) — into
//! `seq (f n) (shift n) − seq L (shift n)` at cost `((2+K₁)+2)/(n+1)`, mirrors
//! that for the `g`/`M` side at cost `((2+K₂)+2)/(n+1)`, then combines the two
//! components. **The rate constant is not hidden**: the witness is the raw
//! `Nat` expression `((2+K₁)+2)+((2+K₂)+2)`, reported honestly rather than
//! simplified to a nicer-looking closed form.
//!
//! [`declare_converges_neg`] is the cheap case the module doc for
//! [`CReal.converges_neg`](super::CRealPrelude::converges_neg) promises:
//! `neg` is pointwise (no shift), so it is exactly
//! [`super::declare_negation`]'s `neg_congr` per-`n` step
//! (`Rat.bounds_neg` plus `Rat.neg_sub`/`Rat.sub_neg_sub`), wrapped in
//! `Converges`'s existential — no shift bridge at all.
//!
//! [`declare_converges_sub`] is immediate from the two: `Converges g M →
//! Converges (fun n => neg (g n)) (neg M)` by [`declare_converges_neg`], then
//! [`declare_converges_add`] applied to `f` and `neg ∘ g`. There is no
//! `CReal.sub` operation in this development (`declare_addition` only ever
//! built `add`), so the difference is spelled `add _ (neg _)` throughout,
//! honestly rather than inventing a `sub` this module does not need.
//!
//! ## `CReal.converges_mul`, and the two obstructions it took to close
//!
//! An earlier slice of this module reported the product as needing "an
//! explicit boundedness hypothesis stated up front", by analogy with
//! `CReal.mul`'s own regularity estimate needing a bound on one multiplicand
//! ([`CReal.mulShift`](super::CRealPrelude::mul_shift)'s construction). A
//! later slice showed that framing wrong: [`declare_converges_bounded`]
//! discharges a boundedness hypothesis for free from `Converges` itself, no
//! choice involved. The REAL obstruction is sharper: `mul (f n) (g n)` and
//! `mul L M` sample their two factors at *different* deep indices
//! (`mulShift (f n) (g n)` varies with `n`; `mulShift L M` is the fixed
//! `bound L + bound M + 1`), so bounding the difference needs a cross-index
//! estimate between two indices *neither* of which is `n` — exactly the
//! "arbitrary-third-index plus Archimedean" machinery
//! [`product`](self::product)'s own module documentation names as the reason
//! `mul_assoc`/`left_distrib`/`mul_congr` needed it.
//!
//! That machinery — [`product::declare_equiv_of_bounded`],
//! [`product::regular_between`], [`product::product_gap`] — was already
//! built and exposed by the time this slice ran (widened to `pub(super)`,
//! not re-derived). [`converges_mul`](Self::converges_mul) below reuses it
//! directly: [`bounded_at_index`] widens `Bounded f`'s per-`n` bound to a
//! bound uniform in any further sampling index, and [`converges_gap_at`] is
//! the `Converges`-hypothesis analogue of [`product::cross_gap`]'s
//! `Equiv`-hypothesis telescope. See the comment immediately above
//! [`declare_converges_mul`] for the full derivation and the raw witness.
//!
//! ## `CReal.continuous_mul`, `CReal.continuous_comp`, and why the
//! trisection step for the approximate IVT is **not** in this file
//!
//! [`declare_continuous_mul`] and [`declare_continuous_comp`] transfer
//! straight from [`converges_mul`](Self::converges_mul) and from chaining
//! two [`ContinuousAt`](Self::continuous_at) witnesses respectively — no new
//! rational estimate in either, exactly like [`declare_continuous_add`].
//!
//! The intended next step was the single-step trisection lemma for the
//! approximate intermediate value theorem: from `f p < 0`, `0 < f q` and
//! `p ≤ m₁ < m₂ ≤ q`, decide `f m₁ < 0 ∨ 0 < f m₂` via
//! [`CReal.lt_cotrans`](Self::lt_cotrans), producing a subinterval of `2/3`
//! the width on which `f` still changes sign. **This exact disjunction is
//! false**, and not merely hard to formalise: take `f p = −1`, `f q = 1`,
//! and `f m₁ = f m₂ = 0` (a legitimate, perfectly continuous instance — a
//! straight line from `−1` to `1` passes through `0` at an interior point).
//! Neither `f m₁ < 0` nor `0 < f m₂` holds, so the disjunction is false for
//! this instance, so it cannot be a theorem for arbitrary `m₁, m₂`.
//!
//! Concretely, `lt_cotrans` applied to `f p < 0` at `z := f m₁` and to
//! `0 < f q` at `z := f m₂` (the two calls that would decide the two
//! interior points) each reduce, per
//! [`cotransitivity`](super::cotransitivity)'s own module documentation, to
//! comparing a *rational* sample of `z` against a threshold fixed by the
//! **source** hypothesis's gap (`f p` vs. `0`, or `0` vs. `f q`) — not
//! against `0` itself. At the instance above both calls return their
//! "uninformative" disjunct (`f p < f m₁` and `f m₂ < f q`, both trivially
//! true), and neither says anything about the sign of `f m₁` or `f m₂`. No
//! chaining of further `lt_cotrans` calls against `f p`, `f q`, `f m₁` or
//! `f m₂` alone recovers the sign, because the instance above is consistent
//! with every such comparison — deciding a real's sign against a fixed
//! external threshold is exactly what cotransitivity does *not* give you
//! (that is `lt_cotrans`'s whole point: it is not `∀ x, lt x 0 ∨ lt 0 x`).
//!
//! This is consistent with (not a rediscovery of) the reason the *exact*
//! IVT fails: the degenerate instance above is precisely a case where the
//! root is already sitting at `m₁` and `m₂` (`f m₁ = f m₂ = 0`), and no
//! finite decision at those two points can distinguish "the root is exactly
//! here" from "the root is on one side, and this pair of samples happened
//! to land exactly on the old threshold". The **approximate** IVT is still
//! presumably true — a construction that carries the target `ε` through
//! the recursion from the start (rather than testing against literal `0`
//! at every step) should route around this instance, since `f m₁ = f m₂ =
//! 0` is already a valid witness for *any* `ε > 0` — but completing that
//! construction needs more than a bare `lt_cotrans` call at `0`, and this
//! slice did not find and verify a sound version of it. Nothing about
//! `CReal.ContinuousAt`'s sequential (modulus-free) shape was needed to
//! reach this obstruction — it is a fact about `CReal.lt`/`lt_cotrans`
//! alone, prior to any use of continuity.

#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::completeness::half_shift_le;
use super::product::{cmul, fuse_at, index_le, mul_index, mul_shift, product_gap, regular_between};
use super::{
    CRealPrelude, DERIVED_HEIGHT, and_intro, creal_ty, div_succ, embed, equiv, halves, modulus,
    sample, shift, weaken, within,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::{rsub, rsum, rsum_append, rsum_perm};
use crate::rat_prelude::ops::{
    nat_eq_to_rat, nat_rewrite_prop, radd, rat_eq_rewrite, rchain, rcongr, rle, rmul, rneg, rsymm,
    rzero,
};

/// Admit `CReal.Converges`, `CReal.converges_unique`, `CReal.converges_of_const`,
/// `CReal.Cauchy`, `CReal.converges_cauchy`, the algebra of limits,
/// `CReal.Bounded`/`converges_bounded`, `CReal.converges_mul`, and sequential
/// `CReal.ContinuousAt` with its two anchors and closure under sums.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_convergence(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_converges(d, p)?;
    declare_converges_unique(d, p)?;
    declare_converges_of_close(d, p)?;
    declare_converges_of_const(d, p)?;
    declare_converges_of_equiv(d, p)?;
    declare_cauchy(d, p)?;
    declare_converges_cauchy(d, p)?;
    declare_converges_add(d, p)?;
    declare_converges_neg(d, p)?;
    declare_converges_sub(d, p)?;
    declare_converges_squeeze(d, p)?;
    declare_converges_lower_bound(d, p)?;
    declare_converges_lower_bound_shift(d, p)?;
    declare_converges_upper_bound(d, p)?;
    declare_converges_le(d, p)?;
    declare_bounded(d, p)?;
    declare_converges_bounded(d, p)?;
    declare_converges_mul(d, p)?;
    declare_continuous_at(d, p)?;
    declare_continuous_id(d, p)?;
    declare_continuous_const(d, p)?;
    declare_continuous_add(d, p)?;
    declare_continuous_mul(d, p)?;
    declare_continuous_comp(d, p)
}

// --- shared term builders ----------------------------------------------------

/// `Nat → CReal`.
fn seq_fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    d.arrow(nat, carrier)
}

/// `Rat.natDivSucc k j`, with a **symbolic** `Nat` numerator `k`.
pub(super) fn div_succ_at(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, j])
}

/// `fun n => CReal.seq (f n) n` — the raw `Nat → Rat` diagonal of a
/// `Nat → CReal` sequence, the shape [`super::speedup`]'s `KRegular`/
/// `speedup` toolkit consumes.
fn diagonal(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fn_term = d.apply(f, &[n]);
    let body = sample(d, p, fn_term, n);
    d.lam_fv(n_fv, nat, body)
}

/// `Exists elem_ty predicate`.
///
/// `pub(super)`: reused by `creal/series.rs`'s `sumRange_converges_of_dominated`
/// / `sumRange_comparison_test` to build the `Exists CReal (fun L => …)`
/// target type over `CReal` (not `Nat` — `int_prelude::ops::exists_elim` is
/// hardcoded to `Nat`), rather than re-deriving this construction a second
/// time.
pub(super) fn exists_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    elem_ty: ExprId,
    predicate: ExprId,
) -> ExprId {
    let one = d.level_one();
    let exists_name = p.rat.int.logic.exists_;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists_const, &[elem_ty, predicate])
}

/// `Exists.intro elem_ty predicate witness proof`.
///
/// `pub(super)`: reused by `creal/exponential.rs`'s `declare_e_converges`,
/// which builds a CONCRETE `Converges expSeriesPartial e` directly (not
/// through [`declare_converges_of_cauchy`]'s own `Exists`-wrapped route,
/// since the witness there must be the exact declared `e`, not an opaque
/// existential) and needs this exact constructor.
pub(super) fn exists_intro(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    elem_ty: ExprId,
    predicate: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let one = d.level_one();
    let intro_name = p.rat.int.logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[elem_ty, predicate, witness, proof])
}

/// `Exists.rec elem_ty predicate motive minor witness` — eliminate
/// `witness : Exists elem_ty predicate` into `target`, given
/// `minor : ∀ a, predicate a → target`. `target` must not depend on `witness`.
///
/// `pub(super)`: `series.rs`'s `sumRange_comparison_test` reuses this (over
/// `elem_ty := CReal`) to eliminate its `Exists (fun M => Converges (sumRange
/// b) M)` hypothesis into `Cauchy (sumRange b)` — a target that does not
/// mention the witness `M`, the same "target independent of the witness"
/// shape `series.rs`'s own `sumRange_cauchy_of_dominated` already uses
/// against a *different* existential, over `Nat`.
pub(super) fn exists_elim(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    elem_ty: ExprId,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let one = d.level_one();
    let exists_name = p.rat.int.logic.exists_;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    let exists_type = d.apply(exists_const, &[elem_ty, predicate]);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, exists_type, target)
    };
    let rec_name = p.rat.int.logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[elem_ty, predicate, motive, minor, witness])
}

// --- `CReal.Converges` --------------------------------------------------------

/// `∀ n, Within (seq (func n) n − seq target n) (natDivSucc k n)`, for a
/// (possibly symbolic) numerator `k`.
fn converges_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    func: ExprId,
    target: ExprId,
    k: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fn_term = d.apply(func, &[n]);
    let left = sample(d, p, fn_term, n);
    let right = sample(d, p, target, n);
    let difference = rsub(d, rat, left, right);
    let bound = div_succ_at(d, p, k, n);
    let claim = within(d, p, difference, bound);
    d.pi_fv(n_fv, nat, claim)
}

/// `λ K, ∀ n, Within (seq (func n) n − seq target n) (natDivSucc K n)`.
///
/// `pub(super)`: reused by `creal/exponential.rs`'s `declare_e_converges` (see
/// [`exists_intro`]'s doc for why that declaration cannot go through
/// [`declare_converges_of_cauchy`]'s own `Exists`-wrapped route).
pub(super) fn converges_predicate(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    func: ExprId,
    target: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = converges_body(d, p, func, target, k);
    d.lam_fv(k_fv, nat, body)
}

/// `CReal.Converges func target`.
///
/// `pub(super)`: reused by `creal/series.rs`, see [`exists_ty`]'s doc comment.
pub(super) fn converges_applied(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    func: ExprId,
    target: ExprId,
) -> ExprId {
    d.const_app(p.converges, &[func, target])
}

/// `CReal.Converges (f : Nat → CReal) (L : CReal) : Prop :=
///   ∃ (K : Nat), ∀ (n : Nat), Within (seq (f n) n − seq L n) (Rat.natDivSucc K n)`.
///
/// See the module documentation for why this canonical-sample, free-constant
/// form was chosen over the textbook `∀ k, ∃ N, ∀ n ≥ N, …`.
fn declare_converges(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);

    let predicate = converges_predicate(d, p, f, l);
    let claim_ty = exists_ty(d, p, nat, predicate);
    let value = {
        let with_l = d.lam_fv(l_fv, carrier, claim_ty);
        d.lam_fv(f_fv, seq_ty, with_l)
    };
    let ty = {
        let inner = d.arrow(carrier, prop);
        d.arrow(seq_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.converges,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 33),
    })
}

/// `CReal.converges_unique : ∀ f L M, Converges f L → Converges f M → Equiv L M`.
///
/// **The first theorem of analysis over `CReal`.** Fix `n`; the two
/// hypotheses, instantiated at the *same* `n`, give `Within (seq (f n) n −
/// seq L n) (K₁/(n+1))` and `Within (seq (f n) n − seq M n) (K₂/(n+1))`.
/// Negating the second and adding (`Rat.bounds_neg`, `Rat.bounds_add`) bounds
/// `(seq (f n) n − seq M n)·(−1) + (seq (f n) n − seq L n)`— which the
/// identity `Rat.neg_sub` / `Rat.sub_add_sub` collapses to exactly
/// `seq L n − seq M n` — by `(K₁+K₂)/(n+1)`, uniformly in `n`. That is
/// precisely `CReal.equiv_of_bounded`'s hypothesis, so `Equiv L M` follows in
/// one more step. No arbitrary third index, and no Archimedean lemma over
/// `ℚ`, is needed — the two hypotheses already share the index the goal asks
/// for.
fn declare_converges_unique(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let nat_add = d.prelude().add;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let converges_fl = converges_applied(d, p, f, l);
    let converges_fm = converges_applied(d, p, f, m);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let target = equiv(d, p, l, m);

    let outer_predicate = converges_predicate(d, p, f, l);
    let outer_minor = {
        let k1_fv = d.fresh_fvar();
        let k1 = d.kernel().fvar(k1_fv);
        let h1p_ty = converges_body(d, p, f, l, k1);
        let h1p_fv = d.fresh_fvar();
        let h1p = d.kernel().fvar(h1p_fv);

        let inner_predicate = converges_predicate(d, p, f, m);
        let inner_minor = {
            let k2_fv = d.fresh_fvar();
            let k2 = d.kernel().fvar(k2_fv);
            let h2p_ty = converges_body(d, p, f, m, k2);
            let h2p_fv = d.fresh_fvar();
            let h2p = d.kernel().fvar(h2p_fv);

            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);

            let fn_term = d.apply(f, &[n]);
            let a = sample(d, p, fn_term, n);
            let lseq = sample(d, p, l, n);
            let mseq = sample(d, p, m, n);

            let u = rsub(d, rat, a, lseq);
            let v = rsub(d, rat, a, mseq);
            let bk1 = div_succ_at(d, p, k1, n);
            let bk2 = div_succ_at(d, p, k2, n);

            let within_u = d.apply(h1p, &[n]);
            let within_v = d.apply(h2p, &[n]);

            let (lower_u, upper_u) = halves(d, p, u, bk1, within_u);
            let negu = rneg(d, u);
            let within_negu = d.lemma(rat.bounds_neg, &[u, bk1, lower_u, upper_u]);
            let (lower_negu, upper_negu) = halves(d, p, negu, bk1, within_negu);

            let (lower_v, upper_v) = halves(d, p, v, bk2, within_v);

            let combined = d.lemma(
                rat.bounds_add,
                &[v, bk2, negu, bk1, lower_v, upper_v, lower_negu, upper_negu],
            );
            let sum_u_v = radd(d, v, negu);
            let sum_bound = radd(d, bk2, bk1);

            // Identity: v + (−u) = (a−mseq) + (lseq−a) = lseq − mseq.
            let target_diff = rsub(d, rat, lseq, mseq);
            let negu_eq = d.lemma(rat.neg_sub, &[a, lseq]); // Eq (neg u) (lseq - a)
            let lseq_minus_a = rsub(d, rat, lseq, a);
            let mid1 = radd(d, v, lseq_minus_a);
            let step1 = rcongr(d, negu, lseq_minus_a, negu_eq, &|d, t| radd(d, v, t));

            let comm_eq = d.lemma(rat.add_comm, &[v, lseq_minus_a]); // Eq (v+(lseq-a)) ((lseq-a)+v)
            let mid2 = radd(d, lseq_minus_a, v);

            let sub_add_sub_eq = d.lemma(rat.sub_add_sub, &[lseq, a, mseq]); // Eq ((lseq-a)+(a-mseq)) (lseq-mseq)

            let (_, quantity_eq) = rchain(
                d,
                sum_u_v,
                &[
                    (mid1, step1),
                    (mid2, comm_eq),
                    (target_diff, sub_add_sub_eq),
                ],
            );

            let at_quantity =
                rat_eq_rewrite(d, sum_u_v, target_diff, quantity_eq, combined, &|d, t| {
                    within(d, p, t, sum_bound)
                });

            let ksum = d.const_app(nat_add, &[k2, k1]);
            let bound_final = div_succ_at(d, p, ksum, n);
            let bound_eq = d.lemma(rat.nat_div_succ_add, &[k2, k1, n]);
            let at_final =
                rat_eq_rewrite(d, sum_bound, bound_final, bound_eq, at_quantity, &|d, t| {
                    within(d, p, target_diff, t)
                });

            let per_n = d.lam_fv(n_fv, nat, at_final);
            let equiv_proof = d.lemma(p.equiv_of_bounded, &[l, m, ksum, per_n]);

            let with_h2p = d.lam_fv(h2p_fv, h2p_ty, equiv_proof);
            d.lam_fv(k2_fv, nat, with_h2p)
        };
        let inner_elim = exists_elim(d, p, nat, inner_predicate, target, h2, inner_minor);

        let with_h1p = d.lam_fv(h1p_fv, h1p_ty, inner_elim);
        d.lam_fv(k1_fv, nat, with_h1p)
    };
    let proof_body = exists_elim(d, p, nat, outer_predicate, target, h1, outer_minor);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, converges_fm, proof_body);
        let with_h1 = d.lam_fv(h1_fv, converges_fl, with_h2);
        let with_m = d.lam_fv(m_fv, carrier, with_h1);
        let with_l = d.lam_fv(l_fv, carrier, with_m);
        d.lam_fv(f_fv, seq_ty, with_l)
    };
    let ty = {
        let after_h2 = d.arrow(converges_fm, target);
        let after_h1 = d.arrow(converges_fl, after_h2);
        let with_m = d.pi_fv(m_fv, carrier, after_h1);
        let with_l = d.pi_fv(l_fv, carrier, with_m);
        d.pi_fv(f_fv, seq_ty, with_l)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_unique,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.converges_of_close : ∀ f g L (Kc : Nat), (∀ n, Within (seq (g n) n
/// − seq (f n) n) (Rat.natDivSucc Kc n)) → Converges f L → Converges g L`.
///
/// See [`CRealPrelude::converges_of_close`] for the statement and the
/// one-`Exists.rec` idiom this reuses from [`declare_converges_unique`],
/// simplified: only ONE hypothesis is eliminated (`Converges f L`; the
/// target `Converges g L` does not mention its witness `K`), and the
/// pointwise step is the plain forward triangle identity
/// `Rat.sub_add_sub` — `(g_n − f_n) + (f_n − L_n) = g_n − L_n` — rather than
/// `converges_unique`'s negated `L − M` shape, so no `Rat.bounds_neg` step
/// is needed: `Rat.bounds_add` combines the two halved bounds directly.
fn declare_converges_of_close(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let nat_add = d.prelude().add;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let kc_fv = d.fresh_fvar();
    let kc = d.kernel().fvar(kc_fv);

    // cross_ty : ∀ n, Within (seq (g n) n − seq (f n) n) (natDivSucc kc n).
    let cross_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let g_term = d.apply(g, &[n]);
        let gseq = sample(d, p, g_term, n);
        let f_term = d.apply(f, &[n]);
        let fseq = sample(d, p, f_term, n);
        let diff = rsub(d, rat, gseq, fseq);
        let bound = div_succ_at(d, p, kc, n);
        let claim = within(d, p, diff, bound);
        d.pi_fv(n_fv, nat, claim)
    };
    let cross_fv = d.fresh_fvar();
    let cross = d.kernel().fvar(cross_fv);

    let converges_fl = converges_applied(d, p, f, l);
    let hconv_fv = d.fresh_fvar();
    let hconv = d.kernel().fvar(hconv_fv);

    let target = converges_applied(d, p, g, l);

    let predicate = converges_predicate(d, p, f, l);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = converges_body(d, p, f, l, k);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let g_term = d.apply(g, &[n]);
        let gseq = sample(d, p, g_term, n);
        let f_term = d.apply(f, &[n]);
        let fseq = sample(d, p, f_term, n);
        let lseq = sample(d, p, l, n);

        let u_val = rsub(d, rat, gseq, fseq);
        let v_val = rsub(d, rat, fseq, lseq);

        let bkc = div_succ_at(d, p, kc, n);
        let bk = div_succ_at(d, p, k, n);

        let within_u = d.apply(cross, &[n]);
        let within_v = d.apply(hp, &[n]);

        let (lower_u, upper_u) = halves(d, p, u_val, bkc, within_u);
        let (lower_v, upper_v) = halves(d, p, v_val, bk, within_v);

        let combined = d.lemma(
            rat.bounds_add,
            &[u_val, bkc, v_val, bk, lower_u, upper_u, lower_v, upper_v],
        );
        // combined : Within (u_val + v_val) (bkc + bk).
        let sum_uv = radd(d, u_val, v_val);
        let target_diff = rsub(d, rat, gseq, lseq);
        let sub_add_sub_eq = d.lemma(rat.sub_add_sub, &[gseq, fseq, lseq]);
        let bkc_plus_bk = radd(d, bkc, bk);
        let at_target =
            rat_eq_rewrite(d, sum_uv, target_diff, sub_add_sub_eq, combined, &|d, t| {
                within(d, p, t, bkc_plus_bk)
            });

        let ksum = d.const_app(nat_add, &[kc, k]);
        let bound_final = div_succ_at(d, p, ksum, n);
        let bound_eq = d.lemma(rat.nat_div_succ_add, &[kc, k, n]);
        let at_final = rat_eq_rewrite(d, bkc_plus_bk, bound_final, bound_eq, at_target, &|d, t| {
            within(d, p, target_diff, t)
        });

        let per_n = d.lam_fv(n_fv, nat, at_final);
        let predicate_g = converges_predicate(d, p, g, l);
        let intro = exists_intro(d, p, nat, predicate_g, ksum, per_n);

        let with_hp = d.lam_fv(hp_fv, hp_ty, intro);
        d.lam_fv(k_fv, nat, with_hp)
    };
    let proof_body = exists_elim(d, p, nat, predicate, target, hconv, minor);

    let value = {
        let with_hconv = d.lam_fv(hconv_fv, converges_fl, proof_body);
        let with_cross = d.lam_fv(cross_fv, cross_ty, with_hconv);
        let with_kc = d.lam_fv(kc_fv, nat, with_cross);
        let with_l = d.lam_fv(l_fv, carrier, with_kc);
        let with_g = d.lam_fv(g_fv, seq_ty, with_l);
        d.lam_fv(f_fv, seq_ty, with_g)
    };
    let ty = {
        let after_hconv = d.arrow(converges_fl, target);
        let after_cross = d.arrow(cross_ty, after_hconv);
        let after_kc = d.pi_fv(kc_fv, nat, after_cross);
        let after_l = d.pi_fv(l_fv, carrier, after_kc);
        let after_g = d.pi_fv(g_fv, seq_ty, after_l);
        d.pi_fv(f_fv, seq_ty, after_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_of_close,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.converges_of_const : ∀ c, Converges (fun _ => c) c`.
///
/// The witness constant is `0`: `seq ((fun _ => c) n) n` beta-reduces to
/// `seq c n`, so the difference is `Rat.sub_self`-zero at every index, and
/// `Within 0 (natDivSucc 0 n)` is `Rat.zero_le_nat_div_succ` in both halves.
fn declare_converges_of_const(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let const_seq = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, nat, c)
    };

    let zero_nat = d.num(0);

    let per_n = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let point = sample(d, p, c, n);
        let difference = rsub(d, rat, point, point);
        let bound = div_succ(d, p, 0, n);
        let zero = rzero(d, rat);

        let self_eq = d.lemma(rat.sub_self, &[point]); // Eq difference zero
        let back = rsymm(d, difference, zero, self_eq); // Eq zero difference

        let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[zero_nat, n]); // 0 ≤ bound
        let nonpos = d.lemma(rat.neg_nonpos_of_nonneg, &[bound, nonneg]); // -bound ≤ 0
        let negated_bound = rneg(d, bound);

        let lower = rat_eq_rewrite(d, zero, difference, back, nonpos, &|d, t| {
            rle(d, rat, negated_bound, t)
        });
        let upper = rat_eq_rewrite(d, zero, difference, back, nonneg, &|d, t| {
            rle(d, rat, t, bound)
        });

        let lower_ty = rle(d, rat, negated_bound, difference);
        let upper_ty = rle(d, rat, difference, bound);
        let claim = and_intro(d, p, lower_ty, upper_ty, lower, upper);
        d.lam_fv(n_fv, nat, claim)
    };

    let predicate = converges_predicate(d, p, const_seq, c);
    let claim = exists_intro(d, p, nat, predicate, zero_nat, per_n);

    let ty = {
        let applied = converges_applied(d, p, const_seq, c);
        d.pi_fv(c_fv, carrier, applied)
    };
    let value = d.lam_fv(c_fv, carrier, claim);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_of_const,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.converges_of_equiv : ∀ f target, (∀ n, Equiv (f n) target) →
/// Converges f target`.
///
/// A `Nat → CReal` sequence each of whose terms is EXACTLY `Equiv` to a fixed
/// `target` — not merely close for large `n`, but for EVERY `n` — trivially
/// `Converges` to it, at the fixed rate `K := 2`. `Equiv (f n) target`
/// unfolds to `∀ j, Within (seq (f n) j − seq target j) (natDivSucc 2 j)`
/// ([`super::equiv`]'s own definition); instantiating that at `j := n` is
/// already exactly `Converges`'s own per-index bound at `K = 2`
/// ([`converges_body`]) — no index shift, no estimate, no dependence on `f`
/// beyond the hypothesis itself.
///
/// This is the second half of the general "speedup transported" bridge
/// [`declare_converges_of_scaled_cauchy`] provides the first half of:
/// together with `CReal.converges_unique`, a sequence that is (a) EXACTLY
/// `Equiv` to a known constant at every index and (b) the diagonal input to
/// some `CReal.mk (speedup … K) …` construction lets a caller conclude that
/// constructed `CReal` is `Equiv` to the known constant, with no new
/// epsilon estimate anywhere. `creal/integral.rs`'s `CReal.integral_const`
/// is the first such caller — `CReal.riemannSum_const` supplies exactly this
/// pointwise-equiv hypothesis against `mul c (b−a)`, for every subdivision
/// count, not just in the limit.
fn declare_converges_of_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let target_fv = d.fresh_fvar();
    let target = d.kernel().fvar(target_fv);

    let hyp_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let claim = equiv(d, p, fn_term, target);
        d.pi_fv(n_fv, nat, claim)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let two_nat = d.num(2);

    let per_n = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let hn = d.apply(h, &[n]); // Equiv (f n) target
        let inst = d.apply(hn, &[n]); // Within (seq (f n) n - seq target n) (natDivSucc 2 n)
        d.lam_fv(n_fv, nat, inst)
    };

    let converges_pred = converges_predicate(d, p, f, target);
    let claim = exists_intro(d, p, nat, converges_pred, two_nat, per_n);

    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, claim);
        let with_target = d.lam_fv(target_fv, carrier, with_h);
        d.lam_fv(f_fv, seq_ty, with_target)
    };
    let ty = {
        let concl = converges_applied(d, p, f, target);
        let inner = d.arrow(hyp_ty, concl);
        let with_target = d.pi_fv(target_fv, carrier, inner);
        d.pi_fv(f_fv, seq_ty, with_target)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_of_equiv,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.Cauchy` -----------------------------------------------------------

/// `∀ m n, Within (seq (func m) m − seq (func n) n) (natDivSucc k m + natDivSucc k n)`.
fn cauchy_body(d: &mut IntDev<'_>, p: CRealPrelude, func: ExprId, k: ExprId) -> ExprId {
    let rat = p.rat;
    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fm = d.apply(func, &[m]);
    let fnx = d.apply(func, &[n]);
    let left = sample(d, p, fm, m);
    let right = sample(d, p, fnx, n);
    let difference = rsub(d, rat, left, right);
    let bm = div_succ_at(d, p, k, m);
    let bn = div_succ_at(d, p, k, n);
    let bound = radd(d, bm, bn);
    let claim = within(d, p, difference, bound);
    let over_n = d.pi_fv(n_fv, nat, claim);
    d.pi_fv(m_fv, nat, over_n)
}

/// `λ K, ∀ m n, Within (seq (func m) m − seq (func n) n) (natDivSucc K m + natDivSucc K n)`.
fn cauchy_predicate(d: &mut IntDev<'_>, p: CRealPrelude, func: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = cauchy_body(d, p, func, k);
    d.lam_fv(k_fv, nat, body)
}

/// `CReal.Cauchy func`.
fn cauchy_applied(d: &mut IntDev<'_>, p: CRealPrelude, func: ExprId) -> ExprId {
    d.const_app(p.cauchy, &[func])
}

/// `CReal.Cauchy (f : Nat → CReal) : Prop :=
///   ∃ (K : Nat), ∀ (m n : Nat), Within (seq (f m) m − seq (f n) n)
///     (Rat.natDivSucc K m + Rat.natDivSucc K n)`.
fn declare_cauchy(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let seq_ty = seq_fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let predicate = cauchy_predicate(d, p, f);
    let claim_ty = exists_ty(d, p, nat, predicate);
    let value = d.lam_fv(f_fv, seq_ty, claim_ty);
    let ty = d.arrow(seq_ty, prop);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cauchy,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 34),
    })
}

/// `Eq Rat ((a+b)+(c+e)) ((a+c)+(b+e))` — the "middle four" exchange, the one
/// rearrangement [`declare_converges_cauchy`] needs that a single
/// `Rat.bounds_add` does not supply (three source quantities, not two).
fn regroup_middle_four(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let ce = radd(d, c, e);
    let start = {
        let ab = radd(d, a, b);
        radd(d, ab, ce)
    };

    // (a+b)+(c+e) = a+(b+(c+e))
    let ab = radd(d, a, b);
    let step1 = d.lemma(rat.add_assoc, &[a, b, ce]);
    let b_ce = radd(d, b, ce);
    let mid1 = radd(d, a, b_ce);

    // b+(c+e) = (b+c)+e
    let bc = radd(d, b, c);
    let bc_e = radd(d, bc, e);
    let assoc2 = d.lemma(rat.add_assoc, &[b, c, e]); // Eq ((b+c)+e) (b+(c+e))
    let flip2 = rsymm(d, bc_e, b_ce, assoc2);
    let step2 = rcongr(d, b_ce, bc_e, flip2, &|d, t| radd(d, a, t));
    let mid2 = radd(d, a, bc_e);

    // b+c = c+b
    let comm3 = d.lemma(rat.add_comm, &[b, c]);
    let cb = radd(d, c, b);
    let cb_e = radd(d, cb, e);
    let step3 = rcongr(d, bc, cb, comm3, &|d, t| {
        let te = radd(d, t, e);
        radd(d, a, te)
    });
    let mid3 = radd(d, a, cb_e);

    // (c+b)+e = c+(b+e)
    let step4 = d.lemma(rat.add_assoc, &[c, b, e]); // Eq ((c+b)+e) (c+(b+e))
    let be = radd(d, b, e);
    let c_be = radd(d, c, be);
    let step4c = rcongr(d, cb_e, c_be, step4, &|d, t| radd(d, a, t));
    let mid4 = radd(d, a, c_be);

    // a+(c+(b+e)) = (a+c)+(b+e)
    let ac = radd(d, a, c);
    let target = radd(d, ac, be);
    let step5 = d.lemma(rat.add_assoc, &[a, c, be]); // Eq ((a+c)+(b+e)) (a+(c+(b+e)))
    let flip5 = rsymm(d, target, mid4, step5);

    let _ = ab;
    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (mid3, step3),
            (mid4, step4c),
            (target, flip5),
        ],
    );
    (target, proof)
}

/// `CReal.converges_cauchy : ∀ f L, Converges f L → Cauchy f`.
///
/// Combines `Within (seq (f m) m − seq L m) (K/(m+1))`,
/// `Within (seq (f n) n − seq L n) (K/(n+1))` (both from the one hypothesis,
/// at `m` and at `n`) with `L`'s own regularity between `m` and `n`
/// ([`CReal.regular`](super::CRealPrelude::regular)) via two `Rat.bounds_add`
/// steps, then [`regroup_middle_four`] and two `Rat.natDivSucc_add` fusions
/// turn the resulting bound into `(K+1)/(m+1) + (K+1)/(n+1)` — `Cauchy f`'s
/// own shape at the witness `K+1`.
fn declare_converges_cauchy(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let nat_add = d.prelude().add;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let converges_fl = converges_applied(d, p, f, l);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let target = cauchy_applied(d, p, f);

    let predicate = converges_predicate(d, p, f, l);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = converges_body(d, p, f, l, k);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let one_nat = d.num(1);
        let k1 = d.const_app(nat_add, &[k, one_nat]);

        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let fm = d.apply(f, &[m]);
        let fnx = d.apply(f, &[n]);
        let a = sample(d, p, fm, m);
        let b = sample(d, p, fnx, n);
        let lm = sample(d, p, l, m);
        let ln = sample(d, p, l, n);

        let u = rsub(d, rat, a, lm);
        let v = rsub(d, rat, b, ln);
        let bk_m = div_succ_at(d, p, k, m);
        let bk_n = div_succ_at(d, p, k, n);

        let within_u = d.apply(hp, &[m]);
        let within_v = d.apply(hp, &[n]);

        let (lower_u, upper_u) = halves(d, p, u, bk_m, within_u);
        let (lower_v, upper_v) = halves(d, p, v, bk_n, within_v);
        let negv = rneg(d, v);
        let within_negv = d.lemma(rat.bounds_neg, &[v, bk_n, lower_v, upper_v]);
        let (lower_negv, upper_negv) = halves(d, p, negv, bk_n, within_negv);

        let uv_combined = d.lemma(
            rat.bounds_add,
            &[
                u, bk_m, negv, bk_n, lower_u, upper_u, lower_negv, upper_negv,
            ],
        );
        let uv_sum = radd(d, u, negv);
        let uv_bound = radd(d, bk_m, bk_n);

        let w = rsub(d, rat, lm, ln);
        let w_bound = modulus(d, p, m, n);
        let within_w = d.lemma(p.regular, &[l, m, n]);
        let (lower_w, upper_w) = halves(d, p, w, w_bound, within_w);

        let (lower_uv, upper_uv) = halves(d, p, uv_sum, uv_bound, uv_combined);
        let combined = d.lemma(
            rat.bounds_add,
            &[
                uv_sum, uv_bound, w, w_bound, lower_uv, upper_uv, lower_w, upper_w,
            ],
        );
        let total_sum = radd(d, uv_sum, w);
        let total_bound = radd(d, uv_bound, w_bound);

        // Identity: (u + (-v)) + w = a - b.
        let target_diff = rsub(d, rat, a, b);
        let negv_eq = d.lemma(rat.neg_sub, &[b, ln]); // Eq (neg v) (ln - b)
        let ln_minus_b = rsub(d, rat, ln, b);
        let mid1 = {
            let inner = radd(d, u, ln_minus_b);
            radd(d, inner, w)
        };
        let step1 = rcongr(d, negv, ln_minus_b, negv_eq, &|d, t| {
            let inner = radd(d, u, t);
            radd(d, inner, w)
        });

        let assoc1 = d.lemma(rat.add_assoc, &[u, ln_minus_b, w]); // Eq ((u+lnb)+w) (u+(lnb+w))
        let lnb_w = radd(d, ln_minus_b, w);
        let mid2 = radd(d, u, lnb_w);

        let comm2 = d.lemma(rat.add_comm, &[ln_minus_b, w]); // Eq (lnb+w) (w+lnb)
        let w_lnb = radd(d, w, ln_minus_b);
        let mid3 = radd(d, u, w_lnb);
        let step3 = rcongr(d, lnb_w, w_lnb, comm2, &|d, t| radd(d, u, t));

        let fuse1 = d.lemma(rat.sub_add_sub, &[lm, ln, b]); // Eq ((lm-ln)+(ln-b)) (lm-b)
        let lm_minus_b = rsub(d, rat, lm, b);
        let mid4 = radd(d, u, lm_minus_b);
        let step4 = rcongr(d, w_lnb, lm_minus_b, fuse1, &|d, t| radd(d, u, t));

        let fuse2 = d.lemma(rat.sub_add_sub, &[a, lm, b]); // Eq ((a-lm)+(lm-b)) (a-b)

        let (_, quantity_eq) = rchain(
            d,
            total_sum,
            &[
                (mid1, step1),
                (mid2, assoc1),
                (mid3, step3),
                (mid4, step4),
                (target_diff, fuse2),
            ],
        );

        let at_quantity =
            rat_eq_rewrite(d, total_sum, target_diff, quantity_eq, combined, &|d, t| {
                within(d, p, t, total_bound)
            });

        // Bound: (bk_m + bk_n) + (bm1 + bn1) -> (bk_m+bm1) + (bk_n+bn1)
        //       -> (k+1)/(m+1) + (k+1)/(n+1).
        let bm1 = div_succ(d, p, 1, m);
        let bn1 = div_succ(d, p, 1, n);
        let (regrouped, regroup_eq) = regroup_middle_four(d, p, bk_m, bk_n, bm1, bn1);

        let km1 = radd(d, bk_m, bm1);
        let kn1 = radd(d, bk_n, bn1);
        let fused_m_ty = div_succ_at(d, p, k1, m);
        let fused_n_ty = div_succ_at(d, p, k1, n);
        let fuse_m = d.lemma(rat.nat_div_succ_add, &[k, one_nat, m]); // Eq (bk_m+bm1) (natDivSucc k1 m)
        let fuse_n = d.lemma(rat.nat_div_succ_add, &[k, one_nat, n]); // Eq (bk_n+bn1) (natDivSucc k1 n)

        let step_fuse_m = rcongr(d, km1, fused_m_ty, fuse_m, &|d, t| radd(d, t, kn1));
        let after_m = radd(d, fused_m_ty, kn1);
        let step_fuse_n = rcongr(d, kn1, fused_n_ty, fuse_n, &|d, t| radd(d, fused_m_ty, t));
        let final_bound = radd(d, fused_m_ty, fused_n_ty);

        let (_, bound_eq) = rchain(
            d,
            total_bound,
            &[
                (regrouped, regroup_eq),
                (after_m, step_fuse_m),
                (final_bound, step_fuse_n),
            ],
        );

        let at_final = rat_eq_rewrite(
            d,
            total_bound,
            final_bound,
            bound_eq,
            at_quantity,
            &|d, t| within(d, p, target_diff, t),
        );

        let per_mn = {
            let over_n = d.lam_fv(n_fv, nat, at_final);
            d.lam_fv(m_fv, nat, over_n)
        };
        let cauchy_pred = cauchy_predicate(d, p, f);
        let witnessed = exists_intro(d, p, nat, cauchy_pred, k1, per_mn);

        let with_hp = d.lam_fv(hp_fv, hp_ty, witnessed);
        d.lam_fv(k_fv, nat, with_hp)
    };

    let proof_body = exists_elim(d, p, nat, predicate, target, h, minor);

    let value = {
        let with_h = d.lam_fv(h_fv, converges_fl, proof_body);
        let with_l = d.lam_fv(l_fv, carrier, with_h);
        d.lam_fv(f_fv, seq_ty, with_l)
    };
    let ty = {
        let after_h = d.arrow(converges_fl, target);
        let with_l = d.pi_fv(l_fv, carrier, after_h);
        d.pi_fv(f_fv, seq_ty, with_l)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_cauchy,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `Cauchy → Converges`, via the raw diagonal and `speedup` --------------
//
// `RegularSeq (X : Nat → CReal)` is the wrong shape for this bridge: routing
// through it needs a `CReal.regular` bridge at the *shallow* outer index
// (`m`/`n`) on top of the Cauchy estimate at the *deep* one, and that bridge
// alone already costs a full `1/(m+1)` per side — `RegularSeq`'s fixed
// modulus has no room left for the deep estimate on top, and no choice of
// reindexing removes the shallow cost (it is `CReal.regular`'s own formula,
// forced by the outer index literally being one of its two arguments). The
// raw diagonal `fun n => seq (f n) n` (a bare `Nat → Rat`) has no such
// bridge — its own sample *is* the deep value, not a resampling of it — so
// [`super::speedup`]'s `KRegular`/`speedup`/`regular_of_kregular`/
// `speedup_close` toolkit (built for `sqrt.rs`, reused verbatim here) closes
// exactly, at the diagonal's own regular_pred rather than at RegularSeq.

/// The `KRegular (diagonal f) K` proof built directly from a `K`-scaled
/// Cauchy witness `h : ∀ m n, Within (seq (f m) m − seq (f n) n) (natDivSucc
/// K m + natDivSucc K n)`. Shared by [`declare_regular_of_scaled_cauchy`]
/// (which packages it through
/// [`CRealPrelude::regular_of_kregular`](super::CRealPrelude::regular_of_kregular))
/// and [`declare_converges_of_cauchy`] (which additionally needs the
/// `KRegular` form itself for
/// [`CRealPrelude::speedup_close`](super::CRealPrelude::speedup_close)).
///
/// `KRegular raw K`'s own bound is `(K+1)/(m+1) + (K+1)/(n+1)` — one more unit
/// than the Cauchy witness supplies at each index — so this widens `h`'s
/// instance at `(m, n)` by one [`RatPrelude::nat_div_succ_le_add_left`] step
/// each side (`K ↦ K+1`, additive, no `Nat.sub`) and combines with
/// `Rat.add_le_add`.
///
/// `pub(super)`: reused by `creal/exponential.rs`'s `declare_e_converges`,
/// which needs `Converges expSeriesPartial e` for the EXACT declared `e` —
/// see [`exists_intro`]'s doc for why `declare_converges_of_cauchy`'s own
/// `Exists`-wrapped route cannot supply that directly.
pub(super) fn kregular_of_cauchy_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    raw: ExprId,
    k: ExprId,
    h: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = d.nat_ty();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let inst = d.apply(h, &[m, n]);
    // inst : Within (seq (f m) m - seq (f n) n) (natDivSucc k m + natDivSucc k n)
    //      = Within (raw m - raw n) (natDivSucc k m + natDivSucc k n), by beta.

    let succ_k = d.succ(k);
    let bound_m = div_succ_at(d, p, k, m);
    let bound_n = div_succ_at(d, p, k, n);
    let target_m = div_succ_at(d, p, succ_k, m);
    let target_n = div_succ_at(d, p, succ_k, n);
    let one_nat = d.num(1);

    let le_m = d.lemma(rat.nat_div_succ_le_add_left, &[k, one_nat, m]);
    let le_n = d.lemma(rat.nat_div_succ_le_add_left, &[k, one_nat, n]);
    let widen = d.lemma(
        rat.add_le_add,
        &[bound_m, target_m, bound_n, target_n, le_m, le_n],
    );

    let raw_m = d.apply(raw, &[m]);
    let raw_n = d.apply(raw, &[n]);
    let diff = rsub(d, rat, raw_m, raw_n);
    let bound = radd(d, bound_m, bound_n);
    let target_bound = radd(d, target_m, target_n);

    let result = weaken(d, p, diff, bound, target_bound, inst, widen);

    let with_n = d.lam_fv(n_fv, nat, result);
    d.lam_fv(m_fv, nat, with_n)
}

/// `CReal.regular_of_scaled_cauchy : ∀ f K, (∀ m n, Within (seq (f m) m −
/// seq (f n) n) (natDivSucc K m + natDivSucc K n)) → Regular (speedup
/// (fun n => seq (f n) n) K)`.
///
/// See [`CRealPrelude::regular_of_scaled_cauchy`](super::CRealPrelude::regular_of_scaled_cauchy)
/// for why this targets `speedup`'s raw diagonal rather than `RegularSeq`.
fn declare_regular_of_scaled_cauchy(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let seq_ty = seq_fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hyp_ty = cauchy_body(d, p, f, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let raw = diagonal(d, p, f);
    let kregular_proof = kregular_of_cauchy_proof(d, p, raw, k, h);
    let proof = d.const_app(p.regular_of_kregular, &[raw, k, kregular_proof]);

    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(f_fv, seq_ty, with_k)
    };
    let ty = {
        let target = d.const_app(p.speedup, &[raw, k]);
        let concl = d.const_app(p.regular_pred, &[target]);
        let inner = d.arrow(hyp_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(f_fv, seq_ty, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.regular_of_scaled_cauchy,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.converges_of_scaled_cauchy : ∀ f K, (∀ m n, Within (seq (f m) m −
/// seq (f n) n) (natDivSucc K m + natDivSucc K n)) → Converges f (CReal.mk
/// (speedup (diagonal f) K) (regular_of_scaled_cauchy f K h))`.
///
/// **The "speedup transported" bridge.** [`declare_regular_of_scaled_cauchy`]
/// (just above) shows a `K`-scaled Cauchy witness `h` makes `speedup
/// (diagonal f) K` `Regular`, i.e. that `CReal.mk (speedup (diagonal f) K) …`
/// is a well-formed `CReal`. This theorem is the companion fact a caller
/// needs to relate THAT specific `CReal` back to the sequence `f` it was
/// built from: `f` itself `Converges` to it. Its whole proof body is
/// [`declare_converges_of_cauchy`]'s own inner `minor` (`speedup_close` at
/// `(raw, K, kregular_proof)`, one `Rat.natDivSucc_add` fusion `(K+1)+1`),
/// reused verbatim — the only difference is that `h` here is a bare
/// hypothesis rather than an eliminated `Cauchy f` witness, so the
/// conclusion can NAME the constructed limit directly instead of hiding it
/// behind an `Exists`. That is exactly what a caller who already built `h`
/// and `K` outside a `Cauchy`-wrapper needs — `creal/integral.rs`'s
/// `CReal.integral_converges` is the first such caller, ties `CReal.integral`
/// itself (built via [`Self::regular_of_scaled_cauchy`]) back to `Converges`
/// with no new estimate, and is the reusable half of the transport any
/// future `integral_*` evaluation law needs (see that declaration's own doc
/// comment).
///
/// [`Self::regular_of_scaled_cauchy`]: super::CRealPrelude::regular_of_scaled_cauchy
fn declare_converges_of_scaled_cauchy(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let seq_ty = seq_fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hyp_ty = cauchy_body(d, p, f, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let raw = diagonal(d, p, f);
    let kregular_proof = kregular_of_cauchy_proof(d, p, raw, k, h);
    let reg_proof = d.const_app(p.regular_of_kregular, &[raw, k, kregular_proof]);
    let speedup_term = d.const_app(p.speedup, &[raw, k]);
    let l_val = d.const_app(p.mk, &[speedup_term, reg_proof]);

    let sc = d.const_app(p.speedup_close, &[raw, k, kregular_proof]);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let raw_n = d.apply(raw, &[n]);
    let speedup_n = d.apply(speedup_term, &[n]);
    let diff_n = rsub(d, rat, raw_n, speedup_n);

    let succ_k = d.succ(k);
    let one_nat = d.num(1);
    let bound_left_n = div_succ_at(d, p, succ_k, n);
    let bound_right_n = div_succ_at(d, p, one_nat, n);
    let sc_n_bound = radd(d, bound_left_n, bound_right_n);

    let sc_n = d.apply(sc, &[n]);
    // sc_n : Within diff_n sc_n_bound
    //      = Within (seq (f n) n - seq l_val n) sc_n_bound, by beta/iota.

    let fuse = d.lemma(rat.nat_div_succ_add, &[succ_k, one_nat, n]);
    let k2 = NatOps::add(d, succ_k, one_nat);
    let target_bound_n = div_succ_at(d, p, k2, n);
    let step = rat_eq_rewrite(d, sc_n_bound, target_bound_n, fuse, sc_n, &|d, t| {
        within(d, p, diff_n, t)
    });
    // step : Within diff_n (natDivSucc k2 n)
    //      = Within (seq (f n) n - seq l_val n) (natDivSucc k2 n).

    let over_n = d.lam_fv(n_fv, nat, step);
    let converges_pred = converges_predicate(d, p, f, l_val);
    let conv_proof = exists_intro(d, p, nat, converges_pred, k2, over_n);
    // conv_proof : Converges f l_val

    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, conv_proof);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(f_fv, seq_ty, with_k)
    };
    // `l_val` embeds `reg_proof`, which embeds `h` (via
    // `kregular_of_cauchy_proof`) — unlike `regular_of_scaled_cauchy`'s own
    // conclusion `Regular (speedup raw K)`, which mentions neither `h` nor
    // any proof term at all. So `concl` genuinely depends on `h` here, and
    // `h` must be bound with `pi_fv`, not `d.arrow`.
    let ty = {
        let concl = converges_applied(d, p, f, l_val);
        let inner = d.pi_fv(h_fv, hyp_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(f_fv, seq_ty, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_of_scaled_cauchy,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.converges_of_cauchy : ∀ f, Cauchy f → Exists (fun L => Converges f L)`.
///
/// **The `Cauchy → Converges` bridge.** Eliminates `Cauchy f`'s witness `K`,
/// builds `L := CReal.mk (speedup (diagonal f) K) (regularity proof)` via
/// [`kregular_of_cauchy_proof`] and
/// [`CRealPrelude::regular_of_kregular`](super::CRealPrelude::regular_of_kregular),
/// and closes `Converges f L` with
/// [`CRealPrelude::speedup_close`](super::CRealPrelude::speedup_close)
/// (`Within (raw n − speedup raw K n) (natDivSucc (K+1) n + natDivSucc 1 n)`,
/// definitionally `Within (seq (f n) n − seq L n) (…)`) plus one
/// `Rat.natDivSucc_add` fusion into the single witness `(K+1)+1`. `L` is not
/// named outside the proof — neither is `Cauchy`'s own `K` — so the
/// conclusion is existential.
fn declare_converges_of_cauchy(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let cauchy_ty = cauchy_applied(d, p, f);
    let cauchy_fv = d.fresh_fvar();
    let cauchy_h = d.kernel().fvar(cauchy_fv);

    let predicate = cauchy_predicate(d, p, f);

    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let conv_l = converges_applied(d, p, f, l);
    let pred_l = d.lam_fv(l_fv, carrier, conv_l);
    let target = exists_ty(d, p, carrier, pred_l);

    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hyp_ty = cauchy_body(d, p, f, k);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let raw = diagonal(d, p, f);
        let kregular_proof = kregular_of_cauchy_proof(d, p, raw, k, h);
        let reg_proof = d.const_app(p.regular_of_kregular, &[raw, k, kregular_proof]);
        let speedup_term = d.const_app(p.speedup, &[raw, k]);
        let l_val = d.const_app(p.mk, &[speedup_term, reg_proof]);

        let sc = d.const_app(p.speedup_close, &[raw, k, kregular_proof]);

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let raw_n = d.apply(raw, &[n]);
        let speedup_n = d.apply(speedup_term, &[n]);
        let diff_n = rsub(d, rat, raw_n, speedup_n);

        let succ_k = d.succ(k);
        let one_nat = d.num(1);
        let bound_left_n = div_succ_at(d, p, succ_k, n);
        let bound_right_n = div_succ_at(d, p, one_nat, n);
        let sc_n_bound = radd(d, bound_left_n, bound_right_n);

        let sc_n = d.apply(sc, &[n]);
        // sc_n : Within diff_n sc_n_bound
        //      = Within (seq (f n) n - seq l_val n) sc_n_bound, by beta/iota.

        let fuse = d.lemma(rat.nat_div_succ_add, &[succ_k, one_nat, n]);
        let k2 = NatOps::add(d, succ_k, one_nat);
        let target_bound_n = div_succ_at(d, p, k2, n);
        let step = rat_eq_rewrite(d, sc_n_bound, target_bound_n, fuse, sc_n, &|d, t| {
            within(d, p, diff_n, t)
        });
        // step : Within diff_n (natDivSucc k2 n)
        //      = Within (seq (f n) n - seq l_val n) (natDivSucc k2 n).

        let over_n = d.lam_fv(n_fv, nat, step);
        let converges_pred = converges_predicate(d, p, f, l_val);
        let conv_proof = exists_intro(d, p, nat, converges_pred, k2, over_n);
        // conv_proof : Converges f l_val

        let outer_proof = exists_intro(d, p, carrier, pred_l, l_val, conv_proof);
        // outer_proof : target

        let with_h = d.lam_fv(h_fv, hyp_ty, outer_proof);
        d.lam_fv(k_fv, nat, with_h)
    };

    let proof_body = exists_elim(d, p, nat, predicate, target, cauchy_h, minor);

    let value = {
        let with_h = d.lam_fv(cauchy_fv, cauchy_ty, proof_body);
        d.lam_fv(f_fv, seq_ty, with_h)
    };
    let ty = {
        let after_h = d.arrow(cauchy_ty, target);
        d.pi_fv(f_fv, seq_ty, after_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_of_cauchy,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.regular_of_scaled_cauchy` and `CReal.converges_of_cauchy`.
/// Run **after** [`super::speedup::declare_speedup`] (`creal.rs`'s wiring):
/// both reuse `CReal.speedup`/`regular_of_kregular`/`speedup_close`, which
/// [`declare_convergence`] runs before `speedup` declares.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_cauchy_convergence(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_regular_of_scaled_cauchy(d, p)?;
    declare_converges_of_scaled_cauchy(d, p)?;
    declare_converges_of_cauchy(d, p)
}

// --- the shift bridge, shared by every algebra-of-limits theorem below ------

/// `Rat.le (modulus (shift n) n) (natDivSucc 2 n)` — `1/(shift n+1) + 1/(n+1)
/// ≤ 2/(n+1)`, widening the first summand via
/// [`half_shift_le`](super::completeness::half_shift_le) (reused from
/// [`super::completeness`], not re-derived) and fusing the two now-equal
/// fractions with `Rat.natDivSucc_add`.
fn shift_regular_le(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let rat = p.rat;
    let sn = shift(d, n);
    let one_sn = div_succ(d, p, 1, sn);
    let one_n = div_succ(d, p, 1, n);
    let h = half_shift_le(d, p, n); // Rat.le one_sn one_n
    let refl = d.lemma(rat.le_refl, &[one_n]);
    let step = d.lemma(rat.add_le_add, &[one_sn, one_n, one_n, one_n, h, refl]);
    // step : Rat.le (one_sn + one_n) (one_n + one_n)
    let sum = radd(d, one_sn, one_n);
    let doubled = radd(d, one_n, one_n);
    let one_nat = d.num(1);
    let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
    let two_n = div_succ(d, p, 2, n);
    rat_eq_rewrite(d, doubled, two_n, fuse, step, &|d, t| rle(d, rat, sum, t))
}

/// `Within (seq x (shift n) − seq x n) (natDivSucc 2 n)` — a single real's own
/// regularity between its own index and Bishop's shift. This is the bridge
/// the previous slice's blocker named: one instance of
/// [`CReal.regular`](super::CRealPrelude::regular) at `(x, shift n, n)` gives
/// `Within (seq x (shift n) − seq x n) (modulus (shift n) n)`, and
/// [`shift_regular_le`] widens the bound to a flat `2/(n+1)`.
fn shift_regular_bound(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, n: ExprId) -> ExprId {
    let rat = p.rat;
    let sn = shift(d, n);
    let source = d.lemma(p.regular, &[x, sn, n]);
    let left = sample(d, p, x, sn);
    let right = sample(d, p, x, n);
    let difference = rsub(d, rat, left, right);
    let bound = modulus(d, p, sn, n);
    let wider = div_succ(d, p, 2, n);
    let order = shift_regular_le(d, p, n);
    weaken(d, p, difference, bound, wider, source, order)
}

// --- `CReal.converges_add` ----------------------------------------------------

/// `CReal.converges_add : ∀ f g L M, Converges f L → Converges g M →
/// Converges (fun n => add (f n) (g n)) (add L M)`.
///
/// See the module documentation for the shift bridge and the rate constant.
/// Each of the two components (`f`/`L`, then `g`/`M`) telescopes three
/// same-denominator terms — the shift bridge on `f n` (or `g n`), the
/// `Converges` hypothesis itself, and the shift bridge on `L` (or `M`),
/// negated — into a single `((2+K)+2)/(n+1)` bound, and the two components
/// combine into one more `Rat.natDivSucc_add` fusion.
fn declare_converges_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let nat_add = d.prelude().add;
    let two_nat = d.num(2);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let fg = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let gn_term = d.apply(g, &[n]);
        let added = d.const_app(p.add, &[fn_term, gn_term]);
        d.lam_fv(n_fv, nat, added)
    };
    let add_lm = d.const_app(p.add, &[l, m]);

    let converges_fl = converges_applied(d, p, f, l);
    let converges_gm = converges_applied(d, p, g, m);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let target = converges_applied(d, p, fg, add_lm);

    let outer_predicate = converges_predicate(d, p, f, l);
    let outer_minor = {
        let k1_fv = d.fresh_fvar();
        let k1 = d.kernel().fvar(k1_fv);
        let hp1_ty = converges_body(d, p, f, l, k1);
        let hp1_fv = d.fresh_fvar();
        let hp1 = d.kernel().fvar(hp1_fv);

        let inner_predicate = converges_predicate(d, p, g, m);
        let inner_minor = {
            let k2_fv = d.fresh_fvar();
            let k2 = d.kernel().fvar(k2_fv);
            let hp2_ty = converges_body(d, p, g, m, k2);
            let hp2_fv = d.fresh_fvar();
            let hp2 = d.kernel().fvar(hp2_fv);

            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let sn = shift(d, n);

            let fn_term = d.apply(f, &[n]);
            let gn_term = d.apply(g, &[n]);

            // --- component A: the f/L side ----------------------------------
            let a1 = sample(d, p, fn_term, sn);
            let a1p = sample(d, p, fn_term, n);
            let l_sn = sample(d, p, l, sn);
            let l_n = sample(d, p, l, n);

            let t1 = rsub(d, rat, a1, a1p);
            let t1_bound = div_succ(d, p, 2, n);
            let t1_proof = shift_regular_bound(d, p, fn_term, n);

            let t2 = rsub(d, rat, a1p, l_n);
            let t2_bound = div_succ_at(d, p, k1, n);
            let t2_proof = d.apply(hp1, &[n]);

            let t3 = rsub(d, rat, l_sn, l_n);
            let t3_bound = div_succ(d, p, 2, n);
            let t3_proof = shift_regular_bound(d, p, l, n);

            let (l1a, u1a) = halves(d, p, t1, t1_bound, t1_proof);
            let (l2a, u2a) = halves(d, p, t2, t2_bound, t2_proof);
            let combined12a = d.lemma(
                rat.bounds_add,
                &[t1, t1_bound, t2, t2_bound, l1a, u1a, l2a, u2a],
            );
            let sum12a = radd(d, t1, t2);
            let bound12a = radd(d, t1_bound, t2_bound);

            let (l3a, u3a) = halves(d, p, t3, t3_bound, t3_proof);
            let negt3 = rneg(d, t3);
            let neg_t3_proof = d.lemma(rat.bounds_neg, &[t3, t3_bound, l3a, u3a]);

            let (l12a, u12a) = halves(d, p, sum12a, bound12a, combined12a);
            let (ln3a, un3a) = halves(d, p, negt3, t3_bound, neg_t3_proof);
            let combined_a = d.lemma(
                rat.bounds_add,
                &[sum12a, bound12a, negt3, t3_bound, l12a, u12a, ln3a, un3a],
            );
            let total_sum_a = radd(d, sum12a, negt3);
            let total_bound_a = radd(d, bound12a, t3_bound);

            // Identity: (t1+t2)+(neg t3) = a1 − l_sn.
            let fuse1a = d.lemma(rat.sub_add_sub, &[a1, a1p, l_n]); // Eq (t1+t2) (a1-l_n)
            let a1_minus_ln = rsub(d, rat, a1, l_n);
            let step1a = rcongr(d, sum12a, a1_minus_ln, fuse1a, &|d, t| radd(d, t, negt3));
            let mid1a = radd(d, a1_minus_ln, negt3);

            let negt3_eqa = d.lemma(rat.neg_sub, &[l_sn, l_n]); // Eq (neg t3) (l_n-l_sn)
            let ln_minus_lsn = rsub(d, rat, l_n, l_sn);
            let step2a = rcongr(d, negt3, ln_minus_lsn, negt3_eqa, &|d, t| {
                radd(d, a1_minus_ln, t)
            });
            let mid2a = radd(d, a1_minus_ln, ln_minus_lsn);

            let fuse2a = d.lemma(rat.sub_add_sub, &[a1, l_n, l_sn]); // Eq ((a1-l_n)+(l_n-l_sn)) (a1-l_sn)
            let target_a = rsub(d, rat, a1, l_sn);

            let (_, quantity_eq_a) = rchain(
                d,
                total_sum_a,
                &[(mid1a, step1a), (mid2a, step2a), (target_a, fuse2a)],
            );
            let at_quantity_a = rat_eq_rewrite(
                d,
                total_sum_a,
                target_a,
                quantity_eq_a,
                combined_a,
                &|d, t| within(d, p, t, total_bound_a),
            );

            // Bound: (2/(n+1)+K1/(n+1)) + 2/(n+1) -> ((2+K1)+2)/(n+1).
            let fuse_bound1a = d.lemma(rat.nat_div_succ_add, &[two_nat, k1, n]);
            let ca_inner = d.const_app(nat_add, &[two_nat, k1]);
            let bound12a_fused = div_succ_at(d, p, ca_inner, n);
            let step_bound1a = rcongr(d, bound12a, bound12a_fused, fuse_bound1a, &|d, t| {
                radd(d, t, t3_bound)
            });
            let mid_bound_a = radd(d, bound12a_fused, t3_bound);

            let fuse_bound2a = d.lemma(rat.nat_div_succ_add, &[ca_inner, two_nat, n]);
            let ca = d.const_app(nat_add, &[ca_inner, two_nat]);
            let final_bound_a = div_succ_at(d, p, ca, n);

            let (_, bound_eq_a) = rchain(
                d,
                total_bound_a,
                &[(mid_bound_a, step_bound1a), (final_bound_a, fuse_bound2a)],
            );
            let component_a = rat_eq_rewrite(
                d,
                total_bound_a,
                final_bound_a,
                bound_eq_a,
                at_quantity_a,
                &|d, t| within(d, p, target_a, t),
            );

            // --- component B: the g/M side, mirrors A -----------------------
            let b1 = sample(d, p, gn_term, sn);
            let b1p = sample(d, p, gn_term, n);
            let m_sn = sample(d, p, m, sn);
            let m_n = sample(d, p, m, n);

            let s1 = rsub(d, rat, b1, b1p);
            let s1_bound = div_succ(d, p, 2, n);
            let s1_proof = shift_regular_bound(d, p, gn_term, n);

            let s2 = rsub(d, rat, b1p, m_n);
            let s2_bound = div_succ_at(d, p, k2, n);
            let s2_proof = d.apply(hp2, &[n]);

            let s3 = rsub(d, rat, m_sn, m_n);
            let s3_bound = div_succ(d, p, 2, n);
            let s3_proof = shift_regular_bound(d, p, m, n);

            let (l1b, u1b) = halves(d, p, s1, s1_bound, s1_proof);
            let (l2b, u2b) = halves(d, p, s2, s2_bound, s2_proof);
            let combined12b = d.lemma(
                rat.bounds_add,
                &[s1, s1_bound, s2, s2_bound, l1b, u1b, l2b, u2b],
            );
            let sum12b = radd(d, s1, s2);
            let bound12b = radd(d, s1_bound, s2_bound);

            let (l3b, u3b) = halves(d, p, s3, s3_bound, s3_proof);
            let negs3 = rneg(d, s3);
            let neg_s3_proof = d.lemma(rat.bounds_neg, &[s3, s3_bound, l3b, u3b]);

            let (l12b, u12b) = halves(d, p, sum12b, bound12b, combined12b);
            let (ln3b, un3b) = halves(d, p, negs3, s3_bound, neg_s3_proof);
            let combined_b = d.lemma(
                rat.bounds_add,
                &[sum12b, bound12b, negs3, s3_bound, l12b, u12b, ln3b, un3b],
            );
            let total_sum_b = radd(d, sum12b, negs3);
            let total_bound_b = radd(d, bound12b, s3_bound);

            let fuse1b = d.lemma(rat.sub_add_sub, &[b1, b1p, m_n]);
            let b1_minus_mn = rsub(d, rat, b1, m_n);
            let step1b = rcongr(d, sum12b, b1_minus_mn, fuse1b, &|d, t| radd(d, t, negs3));
            let mid1b = radd(d, b1_minus_mn, negs3);

            let negs3_eqb = d.lemma(rat.neg_sub, &[m_sn, m_n]);
            let mn_minus_msn = rsub(d, rat, m_n, m_sn);
            let step2b = rcongr(d, negs3, mn_minus_msn, negs3_eqb, &|d, t| {
                radd(d, b1_minus_mn, t)
            });
            let mid2b = radd(d, b1_minus_mn, mn_minus_msn);

            let fuse2b = d.lemma(rat.sub_add_sub, &[b1, m_n, m_sn]);
            let target_b = rsub(d, rat, b1, m_sn);

            let (_, quantity_eq_b) = rchain(
                d,
                total_sum_b,
                &[(mid1b, step1b), (mid2b, step2b), (target_b, fuse2b)],
            );
            let at_quantity_b = rat_eq_rewrite(
                d,
                total_sum_b,
                target_b,
                quantity_eq_b,
                combined_b,
                &|d, t| within(d, p, t, total_bound_b),
            );

            let fuse_bound1b = d.lemma(rat.nat_div_succ_add, &[two_nat, k2, n]);
            let cb_inner = d.const_app(nat_add, &[two_nat, k2]);
            let bound12b_fused = div_succ_at(d, p, cb_inner, n);
            let step_bound1b = rcongr(d, bound12b, bound12b_fused, fuse_bound1b, &|d, t| {
                radd(d, t, s3_bound)
            });
            let mid_bound_b = radd(d, bound12b_fused, s3_bound);

            let fuse_bound2b = d.lemma(rat.nat_div_succ_add, &[cb_inner, two_nat, n]);
            let cb = d.const_app(nat_add, &[cb_inner, two_nat]);
            let final_bound_b = div_succ_at(d, p, cb, n);

            let (_, bound_eq_b) = rchain(
                d,
                total_bound_b,
                &[(mid_bound_b, step_bound1b), (final_bound_b, fuse_bound2b)],
            );
            let component_b = rat_eq_rewrite(
                d,
                total_bound_b,
                final_bound_b,
                bound_eq_b,
                at_quantity_b,
                &|d, t| within(d, p, target_b, t),
            );

            // --- combine the two components ---------------------------------
            let (la, ua) = halves(d, p, target_a, final_bound_a, component_a);
            let (lb, ub) = halves(d, p, target_b, final_bound_b, component_b);
            let combined_final = d.lemma(
                rat.bounds_add,
                &[
                    target_a,
                    final_bound_a,
                    target_b,
                    final_bound_b,
                    la,
                    ua,
                    lb,
                    ub,
                ],
            );
            let sum_ab = radd(d, target_a, target_b);
            let final_bound_ab = radd(d, final_bound_a, final_bound_b);

            // Identity: (a1-l_sn)+(b1-m_sn) = (a1+b1)-(l_sn+m_sn) — the
            // quantity `seq (fg n) n − seq (add L M) n` definitionally is.
            let split_final = d.lemma(rat.sub_add_add, &[a1, b1, l_sn, m_sn]);
            let ab_sum = radd(d, a1, b1);
            let lm_sum = radd(d, l_sn, m_sn);
            let goal_quantity = rsub(d, rat, ab_sum, lm_sum);
            let back_final = rsymm(d, goal_quantity, sum_ab, split_final);
            let at_goal = rat_eq_rewrite(
                d,
                sum_ab,
                goal_quantity,
                back_final,
                combined_final,
                &|d, t| within(d, p, t, final_bound_ab),
            );

            let k_sum = d.const_app(nat_add, &[ca, cb]);
            let final_witness_bound = div_succ_at(d, p, k_sum, n);
            let fuse_final = d.lemma(rat.nat_div_succ_add, &[ca, cb, n]);
            let per_n = rat_eq_rewrite(
                d,
                final_bound_ab,
                final_witness_bound,
                fuse_final,
                at_goal,
                &|d, t| within(d, p, goal_quantity, t),
            );

            let per_n_lam = d.lam_fv(n_fv, nat, per_n);
            let converges_pred = converges_predicate(d, p, fg, add_lm);
            let witnessed = exists_intro(d, p, nat, converges_pred, k_sum, per_n_lam);

            let with_hp2 = d.lam_fv(hp2_fv, hp2_ty, witnessed);
            d.lam_fv(k2_fv, nat, with_hp2)
        };
        let inner_elim = exists_elim(d, p, nat, inner_predicate, target, h2, inner_minor);

        let with_hp1 = d.lam_fv(hp1_fv, hp1_ty, inner_elim);
        d.lam_fv(k1_fv, nat, with_hp1)
    };
    let proof_body = exists_elim(d, p, nat, outer_predicate, target, h1, outer_minor);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, converges_gm, proof_body);
        let with_h1 = d.lam_fv(h1_fv, converges_fl, with_h2);
        let with_m = d.lam_fv(m_fv, carrier, with_h1);
        let with_l = d.lam_fv(l_fv, carrier, with_m);
        let with_g = d.lam_fv(g_fv, seq_ty, with_l);
        d.lam_fv(f_fv, seq_ty, with_g)
    };
    let ty = {
        let after_h2 = d.arrow(converges_gm, target);
        let after_h1 = d.arrow(converges_fl, after_h2);
        let with_m = d.pi_fv(m_fv, carrier, after_h1);
        let with_l = d.pi_fv(l_fv, carrier, with_m);
        let with_g = d.pi_fv(g_fv, seq_ty, with_l);
        d.pi_fv(f_fv, seq_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_add,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.converges_neg` ----------------------------------------------------

/// `CReal.converges_neg : ∀ f L, Converges f L → Converges (fun n => neg (f
/// n)) (neg L)`.
///
/// Cheap, as promised: `CReal.neg` is pointwise (no index shift — see
/// [`super::declare_negation`]'s own documentation), so `seq (neg (f n)) n =
/// Rat.neg (seq (f n) n)` and `seq (neg L) n = Rat.neg (seq L n)` need no
/// shift bridge at all. The per-`n` step is exactly `neg_congr`'s
/// (`Rat.bounds_neg` plus `Rat.neg_sub`/`Rat.sub_neg_sub`), wrapped in
/// `Converges`'s existential.
fn declare_converges_neg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let converges_fl = converges_applied(d, p, f, l);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let neg_f = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let negated = d.const_app(p.neg, &[fn_term]);
        d.lam_fv(n_fv, nat, negated)
    };
    let neg_l = d.const_app(p.neg, &[l]);

    let target = converges_applied(d, p, neg_f, neg_l);

    let predicate = converges_predicate(d, p, f, l);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = converges_body(d, p, f, l, k);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let fn_term = d.apply(f, &[n]);
        let a = sample(d, p, fn_term, n);
        let ln = sample(d, p, l, n);
        let forward = rsub(d, rat, a, ln);
        let bound = div_succ_at(d, p, k, n);
        let instance = d.apply(hp, &[n]);
        let (lower, upper) = halves(d, p, forward, bound, instance);
        let flipped = d.lemma(rat.bounds_neg, &[forward, bound, lower, upper]);
        let negated_forward = rneg(d, forward);
        let negated_a = rneg(d, a);
        let negated_l = rneg(d, ln);
        let target_diff = rsub(d, rat, negated_a, negated_l);
        // `−(a − ln) = ln − a = (−a) − (−ln)`, exactly `neg_congr`'s identity.
        let swapped = rsub(d, rat, ln, a);
        let first = d.lemma(rat.neg_sub, &[a, ln]);
        let second = {
            let forward_eq = d.lemma(rat.sub_neg_sub, &[a, ln]);
            rsymm(d, target_diff, swapped, forward_eq)
        };
        let (_, chained) = rchain(
            d,
            negated_forward,
            &[(swapped, first), (target_diff, second)],
        );
        let body = rat_eq_rewrite(
            d,
            negated_forward,
            target_diff,
            chained,
            flipped,
            &|d, t| within(d, p, t, bound),
        );

        let per_n = d.lam_fv(n_fv, nat, body);
        let converges_pred = converges_predicate(d, p, neg_f, neg_l);
        let witnessed = exists_intro(d, p, nat, converges_pred, k, per_n);

        let with_hp = d.lam_fv(hp_fv, hp_ty, witnessed);
        d.lam_fv(k_fv, nat, with_hp)
    };

    let proof_body = exists_elim(d, p, nat, predicate, target, h, minor);

    let value = {
        let with_h = d.lam_fv(h_fv, converges_fl, proof_body);
        let with_l = d.lam_fv(l_fv, carrier, with_h);
        d.lam_fv(f_fv, seq_ty, with_l)
    };
    let ty = {
        let after_h = d.arrow(converges_fl, target);
        let with_l = d.pi_fv(l_fv, carrier, after_h);
        d.pi_fv(f_fv, seq_ty, with_l)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_neg,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.converges_sub` ----------------------------------------------------

/// `CReal.converges_sub : ∀ f g L M, Converges f L → Converges g M →
/// Converges (fun n => add (f n) (neg (g n))) (add L (neg M))`.
///
/// Immediate from [`declare_converges_neg`] and [`declare_converges_add`]:
/// `h2 : Converges g M` gives `Converges (fun n => neg (g n)) (neg M)` via
/// `CReal.converges_neg`, and `CReal.converges_add` applied to `f` and
/// `fun n => neg (g n)` closes it. No unpacking of either existential is
/// needed here — this theorem is two applications, not a new estimate. There
/// is no `CReal.sub` in this development (`declare_addition` only ever built
/// `add`), so the difference is spelled `add _ (neg _)`, honestly.
fn declare_converges_sub(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let converges_fl = converges_applied(d, p, f, l);
    let converges_gm = converges_applied(d, p, g, m);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let neg_g = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let gn_term = d.apply(g, &[n]);
        let negated = d.const_app(p.neg, &[gn_term]);
        d.lam_fv(n_fv, nat, negated)
    };
    let neg_m = d.const_app(p.neg, &[m]);

    let fg = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let neg_gn_term = d.apply(neg_g, &[n]);
        let added = d.const_app(p.add, &[fn_term, neg_gn_term]);
        d.lam_fv(n_fv, nat, added)
    };
    let add_l_negm = d.const_app(p.add, &[l, neg_m]);

    let target = converges_applied(d, p, fg, add_l_negm);

    let neg_step = d.lemma(p.converges_neg, &[g, m, h2]);
    let add_step = d.lemma(p.converges_add, &[f, neg_g, l, neg_m, h1, neg_step]);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, converges_gm, add_step);
        let with_h1 = d.lam_fv(h1_fv, converges_fl, with_h2);
        let with_m = d.lam_fv(m_fv, carrier, with_h1);
        let with_l = d.lam_fv(l_fv, carrier, with_m);
        let with_g = d.lam_fv(g_fv, seq_ty, with_l);
        d.lam_fv(f_fv, seq_ty, with_g)
    };
    let ty = {
        let after_h2 = d.arrow(converges_gm, target);
        let after_h1 = d.arrow(converges_fl, after_h2);
        let with_m = d.pi_fv(m_fv, carrier, after_h1);
        let with_l = d.pi_fv(l_fv, carrier, with_m);
        let with_g = d.pi_fv(g_fv, seq_ty, with_l);
        d.pi_fv(f_fv, seq_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_sub,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.converges_squeeze` ------------------------------------------------

/// `CReal.le (func n) (target n)`.
fn le_applied(d: &mut IntDev<'_>, p: CRealPrelude, func: ExprId, target: ExprId) -> ExprId {
    d.const_app(p.le, &[func, target])
}

/// `∀ n, CReal.le (f n) (g n)` — the pointwise hypothesis
/// [`declare_converges_squeeze`] threads through, applied twice at the same
/// index (`(hab n) n`) to reach a *rational* fact, exactly the way
/// [`converges_body`] reaches one from `Converges`'s own witness.
fn le_pointwise_ty(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fn_term = d.apply(f, &[n]);
    let gn_term = d.apply(g, &[n]);
    let claim = le_applied(d, p, fn_term, gn_term);
    d.pi_fv(n_fv, nat, claim)
}

/// `CReal.converges_squeeze : ∀ a b c L, (∀ n, le (a n) (b n)) →
/// (∀ n, le (b n) (c n)) → Converges a L → Converges c L → Converges b L`.
///
/// See the field documentation on
/// [`CRealPrelude::converges_squeeze`](super::CRealPrelude::converges_squeeze)
/// for why no shift bridge is needed. Fix `n`. `(hab n) n` and `(hbc n) n`
/// give `seq (a n) n − seq (b n) n ≤ 2/(n+1)` and `seq (b n) n − seq (c n) n
/// ≤ 2/(n+1)` directly — `CReal.le`'s own canonical-sample shape. Negating
/// the first (`Rat.neg_le_neg` + `Rat.neg_sub`) and adding it to
/// `Converges a L`'s lower half telescopes (`Rat.sub_add_sub`) to `Rat.le
/// (neg ((2+K_a)/(n+1))) (seq (b n) n − seq L n)`; adding the second to
/// `Converges c L`'s upper half telescopes to `Rat.le (seq (b n) n − seq L
/// n) ((2+K_c)/(n+1))`. Both bounds widen (`Rat.natDivSucc_le_add_left`, one
/// `Nat.add_comm` to line the two additions up) to the single witness `K :=
/// (2+K_a)+(2+K_c)`, and `And.intro` closes `Within` at `K`.
fn declare_converges_squeeze(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let nat_add = d.prelude().add;
    let nat_p = d.prelude();
    let two_nat = d.num(2);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);

    let hab_ty = le_pointwise_ty(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hbc_ty = le_pointwise_ty(d, p, b, c);
    let hbc_fv = d.fresh_fvar();
    let hbc = d.kernel().fvar(hbc_fv);

    let converges_al = converges_applied(d, p, a, l);
    let converges_cl = converges_applied(d, p, c, l);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let target = converges_applied(d, p, b, l);

    let outer_predicate = converges_predicate(d, p, a, l);
    let outer_minor = {
        let k1_fv = d.fresh_fvar();
        let k1 = d.kernel().fvar(k1_fv);
        let hp1_ty = converges_body(d, p, a, l, k1);
        let hp1_fv = d.fresh_fvar();
        let hp1 = d.kernel().fvar(hp1_fv);

        let inner_predicate = converges_predicate(d, p, c, l);
        let inner_minor = {
            let k2_fv = d.fresh_fvar();
            let k2 = d.kernel().fvar(k2_fv);
            let hp2_ty = converges_body(d, p, c, l, k2);
            let hp2_fv = d.fresh_fvar();
            let hp2 = d.kernel().fvar(hp2_fv);

            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);

            let a_n = d.apply(a, &[n]);
            let b_n = d.apply(b, &[n]);
            let c_n = d.apply(c, &[n]);

            let an = sample(d, p, a_n, n);
            let bn = sample(d, p, b_n, n);
            let cn = sample(d, p, c_n, n);
            let ln = sample(d, p, l, n);

            // Converges hypotheses, instantiated at n.
            let gap_al = rsub(d, rat, an, ln);
            let bound_al = div_succ_at(d, p, k1, n);
            let proof_al = d.apply(hp1, &[n]);
            let (lower_al, _upper_al) = halves(d, p, gap_al, bound_al, proof_al);

            let gap_cl = rsub(d, rat, cn, ln);
            let bound_cl = div_succ_at(d, p, k2, n);
            let proof_cl = d.apply(hp2, &[n]);
            let (_lower_cl, upper_cl) = halves(d, p, gap_cl, bound_cl, proof_cl);

            // `le` hypotheses, applied at their own value's index and then
            // again at `n` — `CReal.le`'s own canonical-sample shape.
            let le_ab_n = d.apply(hab, &[n]);
            let le_ab_nn = d.apply(le_ab_n, &[n]); // Rat.le (an-bn) (2/(n+1))
            let le_bc_n = d.apply(hbc, &[n]);
            let le_bc_nn = d.apply(le_bc_n, &[n]); // Rat.le (bn-cn) (2/(n+1))

            let two_n = div_succ(d, p, 2, n);
            let target_diff = rsub(d, rat, bn, ln);

            // --- lower half: bn-ln >= -(2+k1)/(n+1) -------------------------
            let ab_diff = rsub(d, rat, an, bn);
            let neg_ab_step = d.lemma(rat.neg_le_neg, &[ab_diff, two_n, le_ab_nn]);
            // neg_ab_step : Rat.le (neg two_n) (neg ab_diff)
            let ba_diff = rsub(d, rat, bn, an);
            let neg_ab_eq = d.lemma(rat.neg_sub, &[an, bn]); // Eq (neg ab_diff) ba_diff
            let neg_two_n = rneg(d, two_n);
            let neg_ab_diff = rneg(d, ab_diff);
            let fact3p =
                rat_eq_rewrite(d, neg_ab_diff, ba_diff, neg_ab_eq, neg_ab_step, &|d, t| {
                    rle(d, rat, neg_two_n, t)
                });
            // fact3p : Rat.le neg_two_n ba_diff

            let neg_bound_al = rneg(d, bound_al);
            let combined_lower = d.lemma(
                rat.add_le_add,
                &[neg_two_n, ba_diff, neg_bound_al, gap_al, fact3p, lower_al],
            );
            // combined_lower : Rat.le (neg_two_n + neg bound_al) (ba_diff + gap_al)
            let lhs_sum_lower = radd(d, neg_two_n, neg_bound_al);
            let rhs_sum_lower = radd(d, ba_diff, gap_al);
            let identity_lower = d.lemma(rat.sub_add_sub, &[bn, an, ln]); // Eq (ba_diff+gap_al) target_diff
            let step_lower = rat_eq_rewrite(
                d,
                rhs_sum_lower,
                target_diff,
                identity_lower,
                combined_lower,
                &|d, t| rle(d, rat, lhs_sum_lower, t),
            );
            // step_lower : Rat.le lhs_sum_lower target_diff

            let sum_al = radd(d, two_n, bound_al);
            let neg_sum_al = rneg(d, sum_al);
            let neg_add_eq = d.lemma(rat.neg_add, &[two_n, bound_al]); // Eq neg_sum_al lhs_sum_lower
            let eq_lhs_rev = rsymm(d, neg_sum_al, lhs_sum_lower, neg_add_eq);
            let step_lower2 = rat_eq_rewrite(
                d,
                lhs_sum_lower,
                neg_sum_al,
                eq_lhs_rev,
                step_lower,
                &|d, t| rle(d, rat, t, target_diff),
            );
            // step_lower2 : Rat.le neg_sum_al target_diff

            let c1 = d.const_app(nat_add, &[two_nat, k1]);
            let bound_c1 = div_succ_at(d, p, c1, n);
            let fuse_al = d.lemma(rat.nat_div_succ_add, &[two_nat, k1, n]); // Eq sum_al bound_c1
            let neg_congr_al = rcongr(d, sum_al, bound_c1, fuse_al, &|d, t| rneg(d, t));
            let neg_bound_c1 = rneg(d, bound_c1);
            let step_lower_final = rat_eq_rewrite(
                d,
                neg_sum_al,
                neg_bound_c1,
                neg_congr_al,
                step_lower2,
                &|d, t| rle(d, rat, t, target_diff),
            );
            // step_lower_final : Rat.le neg_bound_c1 target_diff

            // --- upper half: bn-ln <= (2+k2)/(n+1) ---------------------------
            let bc_diff = rsub(d, rat, bn, cn);
            let combined_upper = d.lemma(
                rat.add_le_add,
                &[bc_diff, two_n, gap_cl, bound_cl, le_bc_nn, upper_cl],
            );
            // combined_upper : Rat.le ((bn-cn)+gap_cl) (two_n+bound_cl)
            let bc_cl_sum = radd(d, bc_diff, gap_cl);
            let identity_upper = d.lemma(rat.sub_add_sub, &[bn, cn, ln]); // Eq bc_cl_sum target_diff
            let rhs_sum_upper = radd(d, two_n, bound_cl);
            let step_upper = rat_eq_rewrite(
                d,
                bc_cl_sum,
                target_diff,
                identity_upper,
                combined_upper,
                &|d, t| rle(d, rat, t, rhs_sum_upper),
            );
            // step_upper : Rat.le target_diff rhs_sum_upper

            let c2 = d.const_app(nat_add, &[two_nat, k2]);
            let bound_c2 = div_succ_at(d, p, c2, n);
            let fuse_cl = d.lemma(rat.nat_div_succ_add, &[two_nat, k2, n]); // Eq rhs_sum_upper bound_c2
            let step_upper_final =
                rat_eq_rewrite(d, rhs_sum_upper, bound_c2, fuse_cl, step_upper, &|d, t| {
                    rle(d, rat, target_diff, t)
                });
            // step_upper_final : Rat.le target_diff bound_c2

            // --- widen both halves to the common witness K = c1+c2 ----------
            let k_sum = d.const_app(nat_add, &[c1, c2]);
            let bound_k = div_succ_at(d, p, k_sum, n);

            let widen_c1 = d.lemma(rat.nat_div_succ_le_add_left, &[c1, c2, n]);
            // widen_c1 : Rat.le bound_c1 bound_k
            let neg_widen_c1 = d.lemma(rat.neg_le_neg, &[bound_c1, bound_k, widen_c1]);
            // neg_widen_c1 : Rat.le (neg bound_k) (neg bound_c1)
            let neg_bound_k = rneg(d, bound_k);
            let lower_final = d.lemma(
                rat.le_trans,
                &[
                    neg_bound_k,
                    neg_bound_c1,
                    target_diff,
                    neg_widen_c1,
                    step_lower_final,
                ],
            );
            // lower_final : Rat.le neg_bound_k target_diff

            let c2_plus_c1 = d.const_app(nat_add, &[c2, c1]);
            let widen_c2_raw = d.lemma(rat.nat_div_succ_le_add_left, &[c2, c1, n]);
            // widen_c2_raw : Rat.le bound_c2 (div_succ_at c2_plus_c1 n)
            let comm_c2c1 = d.lemma(nat_p.add_comm, &[c2, c1]); // Eq Nat c2_plus_c1 k_sum
            let widen_c2 =
                nat_rewrite_prop(d, c2_plus_c1, k_sum, comm_c2c1, widen_c2_raw, &|d, t| {
                    let dsum = div_succ_at(d, p, t, n);
                    rle(d, rat, bound_c2, dsum)
                });
            // widen_c2 : Rat.le bound_c2 bound_k
            let upper_final = d.lemma(
                rat.le_trans,
                &[target_diff, bound_c2, bound_k, step_upper_final, widen_c2],
            );
            // upper_final : Rat.le target_diff bound_k

            let lower_ty = rle(d, rat, neg_bound_k, target_diff);
            let upper_ty = rle(d, rat, target_diff, bound_k);
            let within_proof = and_intro(d, p, lower_ty, upper_ty, lower_final, upper_final);

            let per_n = d.lam_fv(n_fv, nat, within_proof);
            let converges_pred = converges_predicate(d, p, b, l);
            let witnessed = exists_intro(d, p, nat, converges_pred, k_sum, per_n);

            let with_hp2 = d.lam_fv(hp2_fv, hp2_ty, witnessed);
            d.lam_fv(k2_fv, nat, with_hp2)
        };
        let inner_elim = exists_elim(d, p, nat, inner_predicate, target, h2, inner_minor);

        let with_hp1 = d.lam_fv(hp1_fv, hp1_ty, inner_elim);
        d.lam_fv(k1_fv, nat, with_hp1)
    };
    let proof_body = exists_elim(d, p, nat, outer_predicate, target, h1, outer_minor);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, converges_cl, proof_body);
        let with_h1 = d.lam_fv(h1_fv, converges_al, with_h2);
        let with_hbc = d.lam_fv(hbc_fv, hbc_ty, with_h1);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hbc);
        let with_l = d.lam_fv(l_fv, carrier, with_hab);
        let with_c = d.lam_fv(c_fv, seq_ty, with_l);
        let with_b = d.lam_fv(b_fv, seq_ty, with_c);
        d.lam_fv(a_fv, seq_ty, with_b)
    };
    let ty = {
        let after_h2 = d.arrow(converges_cl, target);
        let after_h1 = d.arrow(converges_al, after_h2);
        let after_hbc = d.arrow(hbc_ty, after_h1);
        let after_hab = d.arrow(hab_ty, after_hbc);
        let with_l = d.pi_fv(l_fv, carrier, after_hab);
        let with_c = d.pi_fv(c_fv, seq_ty, with_l);
        let with_b = d.pi_fv(b_fv, seq_ty, with_c);
        d.pi_fv(a_fv, seq_ty, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_squeeze,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.converges_lower_bound` / `CReal.converges_upper_bound` --------
//
// The domain-hypothesis question this section answers: for the intended
// `converges_comp` (`Converges f L → UniformlyContinuousOn F a b →
// Converges (F ∘ f) (F L)`), are `le a L`/`le L b` derivable from `∀n, le a
// (f n)`/`∀n, le (f n) b` plus `Converges f L`, or do they need to be
// additional hypotheses? **They are derivable**, by the ordinary
// closed-under-limits argument for a non-strict order, and the two
// declarations below prove it. Unlike the composition itself (see this
// file's own analysis further down for why THAT is not provable in the
// stated form), this needs no inversion of an arbitrary modulus: it is
// `le_trans`'s own "compare at an arbitrary third index `j`" idiom
// (`creal.rs`'s `declare_transitivity`), applied to a four-term telescope
// that routes through `f j` instead of through a second `CReal`.
//
// [`fuse_bridge_bound`] is a verbatim re-derivation of `creal.rs`'s private
// `six_term_bound` (not reusable across the file boundary — same reason
// `half_shift_le` needed widening rather than a second copy, except here the
// original stays `le_trans`-local and this is a fresh copy), generalised
// from two literal-`2` middle terms to two *symbolic* middle numerators —
// `nat_div_succ_add` is already fully generic in its numerators, so nothing
// about the fusion algebra changes, only which `Nat` expressions feed it.

/// `1 + (mid1_num + (mid2_num + 1))` — the fused `Nat` numerator
/// [`fuse_bridge_bound`] produces, computed standalone (cheaply) for the
/// caller that needs it *outside* the per-`j` proof (as the numerator
/// argument to `Rat.le_of_le_add_nat_div_succ`) without re-running the whole
/// bound-fusion proof a second time just to read it off.
fn bridge_total_numerator(d: &mut IntDev<'_>, mid1_num: ExprId, mid2_num: ExprId) -> ExprId {
    let one_nat = d.num(1);
    let s1_num = NatOps::add(d, mid2_num, one_nat);
    let s2_num = NatOps::add(d, mid1_num, s1_num);
    NatOps::add(d, one_nat, s2_num)
}

/// `Eq Rat (modulus outer inner + (natDivSucc mid1_num inner + (natDivSucc
/// mid2_num inner + modulus inner outer))) (natDivSucc 2 outer + natDivSucc
/// k_total inner)`, returned as `(final_bound, k_total, proof)`.
///
/// The bound-fusion half of the standard Bishop "compare at an arbitrary
/// third index" estimate: two `modulus` terms contribute the *outer* index's
/// own `2/(outer+1)` (one `1/(outer+1)` each), and the two middle terms plus
/// the two `modulus` terms' `1/(inner+1)` halves all land on the *inner*
/// index, fusing into a single symbolic numerator ([`bridge_total_numerator`]).
/// See [`declare_converges_lower_bound`] for where the four source facts
/// (regularity, a pointwise `le`, the `Converges` witness, regularity again)
/// come from; this helper only ever sees their bounds.
fn fuse_bridge_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    outer: ExprId,
    inner: ExprId,
    mid1_num: ExprId,
    mid2_num: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);

    let b1 = modulus(d, p, outer, inner);
    let b2 = div_succ_at(d, p, mid1_num, inner);
    let b3 = div_succ_at(d, p, mid2_num, inner);
    let b4 = modulus(d, p, inner, outer);
    let c34 = radd(d, b3, b4);
    let c234 = radd(d, b2, c34);
    let c1234 = radd(d, b1, c234);

    let atom_a = div_succ(d, p, 1, outer);
    let atom_b = div_succ(d, p, 1, inner);
    let flat_atoms = [atom_a, atom_b, b2, b3, atom_b, atom_a];
    let sorted_atoms = [atom_a, atom_a, atom_b, b2, b3, atom_b];
    let flatten = rsum_append(d, rat, &flat_atoms[..2], &flat_atoms[2..]);
    let flat = rsum(d, rat, &flat_atoms);
    let permute = rsum_perm(d, rat, &flat_atoms, &sorted_atoms);
    let sorted = rsum(d, rat, &sorted_atoms);

    // innermost pair: b3 + atom_b -> s1
    let s1_num = NatOps::add(d, mid2_num, one_nat);
    let s1 = div_succ_at(d, p, s1_num, inner);
    let fuse_inner = d.lemma(rat.nat_div_succ_add, &[mid2_num, one_nat, inner]);
    let b3_atomb = radd(d, b3, atom_b);
    let after_inner = rcongr(d, b3_atomb, s1, fuse_inner, &|d, t| {
        let level1 = radd(d, b2, t);
        let level2 = radd(d, atom_b, level1);
        let level3 = radd(d, atom_a, level2);
        radd(d, atom_a, level3)
    });
    let sorted_1 = {
        let level1 = radd(d, b2, s1);
        let level2 = radd(d, atom_b, level1);
        let level3 = radd(d, atom_a, level2);
        radd(d, atom_a, level3)
    };

    // next pair: b2 + s1 -> s2
    let s2_num = NatOps::add(d, mid1_num, s1_num);
    let s2 = div_succ_at(d, p, s2_num, inner);
    let fuse_mid = d.lemma(rat.nat_div_succ_add, &[mid1_num, s1_num, inner]);
    let b2_s1 = radd(d, b2, s1);
    let after_mid = rcongr(d, b2_s1, s2, fuse_mid, &|d, t| {
        let level2 = radd(d, atom_b, t);
        let level3 = radd(d, atom_a, level2);
        radd(d, atom_a, level3)
    });
    let sorted_2 = {
        let level2 = radd(d, atom_b, s2);
        let level3 = radd(d, atom_a, level2);
        radd(d, atom_a, level3)
    };

    // next pair: atom_b + s2 -> s3 (this is `k_total`)
    let s3_num = NatOps::add(d, one_nat, s2_num);
    let s3 = div_succ_at(d, p, s3_num, inner);
    let fuse_outer_j = d.lemma(rat.nat_div_succ_add, &[one_nat, s2_num, inner]);
    let atomb_s2 = radd(d, atom_b, s2);
    let after_outer_j = rcongr(d, atomb_s2, s3, fuse_outer_j, &|d, t| {
        let level3 = radd(d, atom_a, t);
        radd(d, atom_a, level3)
    });
    let sorted_3 = {
        let level3 = radd(d, atom_a, s3);
        radd(d, atom_a, level3)
    };

    // regroup a+(a+s3) = (a+a)+s3, then fuse a+a -> natDivSucc 2 outer.
    let aa = radd(d, atom_a, atom_a);
    let flat_pair = radd(d, aa, s3);
    let regroup = {
        let forward = d.lemma(rat.add_assoc, &[atom_a, atom_a, s3]);
        rsymm(d, flat_pair, sorted_3, forward)
    };
    let fuse_head = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, outer]);
    let goal_bound = div_succ(d, p, 2, outer);
    let after_head = rcongr(d, aa, goal_bound, fuse_head, &|d, t| radd(d, t, s3));
    let final_bound = radd(d, goal_bound, s3);

    let (_, bound_chain) = rchain(
        d,
        c1234,
        &[
            (flat, flatten),
            (sorted, permute),
            (sorted_1, after_inner),
            (sorted_2, after_mid),
            (sorted_3, after_outer_j),
            (flat_pair, regroup),
            (final_bound, after_head),
        ],
    );
    (final_bound, s3_num, bound_chain)
}

/// `Eq Rat ((head−m1)+((m1−m2)+((m2−m3)+(m3−tail)))) (head−tail)` — the
/// four-term difference telescope. A local copy of `creal.rs`'s private
/// `telescope_four` (same reason [`fuse_bridge_bound`] is a local copy of
/// `six_term_bound`): the shape is identical, only the four intermediate
/// points differ per call site.
fn telescope_le4(
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

/// `CReal.converges_lower_bound : ∀ a f L, (∀ n, le a (f n)) → Converges f L
/// → le a L`.
///
/// A non-strict lower bound on a convergent sequence bounds its limit
/// below — the closed-under-limits half of the domain question
/// `converges_comp` needs. Fix `m` (`le a L`'s own index); at an arbitrary
/// third index `j`, `a`'s regularity bridges `seq a m` to `seq a j`,
/// `le a (f j)` (applied at its own index `j`) bridges to `seq (f j) j`,
/// `Converges f L`'s witness bridges to `seq L j`, and `L`'s regularity
/// bridges back to `seq L m`. [`telescope_le4`] collapses the four-term sum
/// to `seq a m − seq L m` exactly, [`fuse_bridge_bound`] collapses the bound
/// to `2/(m+1) + (K+4)/(j+1)`, and `Rat.le_of_le_add_nat_div_succ` (the
/// Archimedean squeeze `le_trans` itself runs on) discharges the residual
/// `(K+4)/(j+1)`, uniformly in `j`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// refused a proof, not that a script gave up.
fn declare_converges_lower_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);

    let lower_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let claim = d.const_app(p.le, &[a, fn_term]);
        d.pi_fv(n_fv, nat, claim)
    };
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);

    let converges_fl = converges_applied(d, p, f, l);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let target_ty = d.const_app(p.le, &[a, l]);

    let predicate = converges_predicate(d, p, f, l);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = converges_body(d, p, f, l, k);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let two_nat = d.num(2);

        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let head = sample(d, p, a, m);
        let tail = sample(d, p, l, m);
        let target = rsub(d, rat, head, tail);
        let goal_bound = div_succ(d, p, 2, m);

        let hypothesis = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);

            let aj = sample(d, p, a, j);
            let fj = d.apply(f, &[j]);
            let fjj = sample(d, p, fj, j);
            let lj = sample(d, p, l, j);

            // u1 : a_m - a_j <= modulus(m,j).
            let u1 = rsub(d, rat, head, aj);
            let b1 = modulus(d, p, m, j);
            let w1 = d.lemma(p.regular, &[a, m, j]);
            let (_, r1) = halves(d, p, u1, b1, w1);

            // u2 : a_j - fjj <= 2/(j+1), directly from h1 at j, at index j.
            let u2 = rsub(d, rat, aj, fjj);
            let b2 = div_succ(d, p, 2, j);
            let h1_at_j = d.apply(h1, &[j]);
            let r2 = d.apply(h1_at_j, &[j]);

            // u3 : fjj - lj <= K/(j+1), the Converges witness's upper half.
            let u3 = rsub(d, rat, fjj, lj);
            let b3 = div_succ_at(d, p, k, j);
            let w3 = d.apply(hp, &[j]);
            let (_, r3) = halves(d, p, u3, b3, w3);

            // u4 : lj - lm <= modulus(j,m).
            let u4 = rsub(d, rat, lj, tail);
            let b4 = modulus(d, p, j, m);
            let w4 = d.lemma(p.regular, &[l, j, m]);
            let (_, r4) = halves(d, p, u4, b4, w4);

            let s34 = d.lemma(rat.add_le_add, &[u3, b3, u4, b4, r3, r4]);
            let q34 = radd(d, u3, u4);
            let c34 = radd(d, b3, b4);
            let s234 = d.lemma(rat.add_le_add, &[u2, b2, q34, c34, r2, s34]);
            let q234 = radd(d, u2, q34);
            let c234 = radd(d, b2, c34);
            let s1234 = d.lemma(rat.add_le_add, &[u1, b1, q234, c234, r1, s234]);
            let q1234 = radd(d, u1, q234);
            let c1234 = radd(d, b1, c234);

            let (_, _, quantity_eq) = telescope_le4(d, p, head, aj, fjj, lj, tail);
            let at_quantity = rat_eq_rewrite(d, q1234, target, quantity_eq, s1234, &|d, t| {
                rle(d, rat, t, c1234)
            });

            let (final_bound, _, bound_eq) = fuse_bridge_bound(d, p, m, j, two_nat, k);
            let moved = rat_eq_rewrite(d, c1234, final_bound, bound_eq, at_quantity, &|d, t| {
                rle(d, rat, target, t)
            });
            d.lam_fv(j_fv, nat, moved)
        };
        let k_total = bridge_total_numerator(d, two_nat, k);
        let at_index = d.lemma(
            rat.le_of_le_add_nat_div_succ,
            &[target, goal_bound, k_total, hypothesis],
        );
        let per_m = d.lam_fv(m_fv, nat, at_index);
        let with_hp = d.lam_fv(hp_fv, hp_ty, per_m);
        d.lam_fv(k_fv, nat, with_hp)
    };

    let proof_body = exists_elim(d, p, nat, predicate, target_ty, h2, minor);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, converges_fl, proof_body);
        let with_h1 = d.lam_fv(h1_fv, lower_ty, with_h2);
        let with_l = d.lam_fv(l_fv, carrier, with_h1);
        let with_f = d.lam_fv(f_fv, seq_ty, with_l);
        d.lam_fv(a_fv, carrier, with_f)
    };
    let ty = {
        let after_h2 = d.arrow(converges_fl, target_ty);
        let after_h1 = d.arrow(lower_ty, after_h2);
        let with_l = d.pi_fv(l_fv, carrier, after_h1);
        let with_f = d.pi_fv(f_fv, seq_ty, with_l);
        d.pi_fv(a_fv, carrier, with_f)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_lower_bound,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.converges_lower_bound_shift : ∀ s a f L, (∀ n, le a (f (Nat.add n
/// s))) → Converges f L → le a L`.
///
/// A genuinely EVENTUAL lower bound, needed because [`declare_converges_lower_bound`]
/// requires its pointwise hypothesis at literally every `n` (including `n =
/// 0`), which a bound coming from monotonicity from some point on cannot
/// supply. Same four-leg telescope as `converges_lower_bound` (`a`'s
/// regularity, the pointwise bound, the `Converges` witness, `L`'s
/// regularity), routed through the SHIFTED index `jp := Nat.add j s` in place
/// of `j` at every leg, then weakened back from `1/(jp+1)` to `1/(j+1)`
/// (`Nat.le j jp` via `Nat.zero_le`/`Nat.add_le_add_right`, `Rat`'s own
/// antitone-in-the-denominator fact [`nat_div_succ_antitone_general`]) so the
/// outer Archimedean squeeze (`Rat.le_of_le_add_nat_div_succ`) still closes on
/// a bound stated in `j` alone, exactly as `converges_lower_bound` needs.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_converges_lower_bound_shift(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);

    let lower_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let shifted_n = NatOps::add(d, n, s);
        let fn_term = d.apply(f, &[shifted_n]);
        let claim = d.const_app(p.le, &[a, fn_term]);
        d.pi_fv(n_fv, nat, claim)
    };
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);

    let converges_fl = converges_applied(d, p, f, l);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let target_ty = d.const_app(p.le, &[a, l]);

    let predicate = converges_predicate(d, p, f, l);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = converges_body(d, p, f, l, k);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let two_nat = d.num(2);

        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let head = sample(d, p, a, m);
        let tail = sample(d, p, l, m);
        let target = rsub(d, rat, head, tail);
        let goal_bound = div_succ(d, p, 2, m);

        let hypothesis = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let jp = NatOps::add(d, j, s);

            let aj = sample(d, p, a, jp);
            let fj = d.apply(f, &[jp]);
            let fjj = sample(d, p, fj, jp);
            let lj = sample(d, p, l, jp);

            // u1 : a_m - a_jp <= modulus(m,jp).
            let u1 = rsub(d, rat, head, aj);
            let b1 = modulus(d, p, m, jp);
            let w1 = d.lemma(p.regular, &[a, m, jp]);
            let (_, r1) = halves(d, p, u1, b1, w1);

            // u2 : a_jp - f(jp)_jp <= 2/(jp+1). `h1` at `n := j` gives `le a
            // (f jp)` (`jp` literally `Nat.add j s`); applying THAT at index
            // `jp` gives the bound at `jp`, not at `j` -- the shift.
            let u2 = rsub(d, rat, aj, fjj);
            let b2 = div_succ(d, p, 2, jp);
            let h1_at_j = d.apply(h1, &[j]);
            let r2 = d.apply(h1_at_j, &[jp]);

            // u3 : f(jp)_jp - L_jp <= K/(jp+1), the Converges witness's upper half.
            let u3 = rsub(d, rat, fjj, lj);
            let b3 = div_succ_at(d, p, k, jp);
            let w3 = d.apply(hp, &[jp]);
            let (_, r3) = halves(d, p, u3, b3, w3);

            // u4 : L_jp - L_m <= modulus(jp,m).
            let u4 = rsub(d, rat, lj, tail);
            let b4 = modulus(d, p, jp, m);
            let w4 = d.lemma(p.regular, &[l, jp, m]);
            let (_, r4) = halves(d, p, u4, b4, w4);

            let s34 = d.lemma(rat.add_le_add, &[u3, b3, u4, b4, r3, r4]);
            let q34 = radd(d, u3, u4);
            let c34 = radd(d, b3, b4);
            let s234 = d.lemma(rat.add_le_add, &[u2, b2, q34, c34, r2, s34]);
            let q234 = radd(d, u2, q34);
            let c234 = radd(d, b2, c34);
            let s1234 = d.lemma(rat.add_le_add, &[u1, b1, q234, c234, r1, s234]);
            let q1234 = radd(d, u1, q234);
            let c1234 = radd(d, b1, c234);

            let (_, _, quantity_eq) = telescope_le4(d, p, head, aj, fjj, lj, tail);
            let at_quantity = rat_eq_rewrite(d, q1234, target, quantity_eq, s1234, &|d, t| {
                rle(d, rat, t, c1234)
            });

            // `final_bound = goal_bound + k_total/(jp+1)`.
            let (final_bound, _, bound_eq) = fuse_bridge_bound(d, p, m, jp, two_nat, k);
            let moved = rat_eq_rewrite(d, c1234, final_bound, bound_eq, at_quantity, &|d, t| {
                rle(d, rat, target, t)
            });

            // Weaken `k_total/(jp+1)` down to `k_total/(j+1)`: `Nat.le j jp`
            // (`j <= j+s`, directly `Nat.le_add_right`), then `Rat`'s
            // antitone-in-the-denominator fact.
            let k_total = bridge_total_numerator(d, two_nat, k);
            let k_total_at_jp = div_succ_at(d, p, k_total, jp);
            let k_total_at_j = div_succ_at(d, p, k_total, j);
            let j_le_jp = d.lemma(rat.int.nat.le_add_right, &[j, s]);
            let antitone = nat_div_succ_antitone_general(d, p, k_total, j, jp, j_le_jp);
            let refl_goal = d.lemma(rat.le_refl, &[goal_bound]);
            let congr = d.lemma(
                rat.add_le_add,
                &[
                    goal_bound,
                    goal_bound,
                    k_total_at_jp,
                    k_total_at_j,
                    refl_goal,
                    antitone,
                ],
            );
            let weakened_bound = radd(d, goal_bound, k_total_at_j);
            let final_hyp = d.lemma(
                rat.le_trans,
                &[target, final_bound, weakened_bound, moved, congr],
            );
            d.lam_fv(j_fv, nat, final_hyp)
        };
        let k_total = bridge_total_numerator(d, two_nat, k);
        let at_index = d.lemma(
            rat.le_of_le_add_nat_div_succ,
            &[target, goal_bound, k_total, hypothesis],
        );
        let per_m = d.lam_fv(m_fv, nat, at_index);
        let with_hp = d.lam_fv(hp_fv, hp_ty, per_m);
        d.lam_fv(k_fv, nat, with_hp)
    };

    let proof_body = exists_elim(d, p, nat, predicate, target_ty, h2, minor);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, converges_fl, proof_body);
        let with_h1 = d.lam_fv(h1_fv, lower_ty, with_h2);
        let with_l = d.lam_fv(l_fv, carrier, with_h1);
        let with_f = d.lam_fv(f_fv, seq_ty, with_l);
        let with_a = d.lam_fv(a_fv, carrier, with_f);
        d.lam_fv(s_fv, nat, with_a)
    };
    let ty = {
        let after_h2 = d.arrow(converges_fl, target_ty);
        let after_h1 = d.arrow(lower_ty, after_h2);
        let with_l = d.pi_fv(l_fv, carrier, after_h1);
        let with_f = d.pi_fv(f_fv, seq_ty, with_l);
        let with_a = d.pi_fv(a_fv, carrier, with_f);
        d.pi_fv(s_fv, nat, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_lower_bound_shift,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.converges_upper_bound : ∀ f L b, (∀ n, le (f n) b) → Converges f L
/// → le L b`.
///
/// The mirror of [`declare_converges_lower_bound`]: an upper bound on a
/// convergent sequence bounds its limit above. Same telescope, run the other
/// way (`L` to `b`, through `f j`), and the `Converges` term is negated
/// (`Rat.bounds_neg` plus `halves`) rather than read directly, since the
/// witness bounds `f j`'s sample *minus* `L`'s, and this telescope needs the
/// difference the other way round.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_converges_upper_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let upper_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let claim = d.const_app(p.le, &[fn_term, b]);
        d.pi_fv(n_fv, nat, claim)
    };
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);

    let converges_fl = converges_applied(d, p, f, l);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let target_ty = d.const_app(p.le, &[l, b]);

    let predicate = converges_predicate(d, p, f, l);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = converges_body(d, p, f, l, k);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let two_nat = d.num(2);

        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let head = sample(d, p, l, m);
        let tail = sample(d, p, b, m);
        let target = rsub(d, rat, head, tail);
        let goal_bound = div_succ(d, p, 2, m);

        let hypothesis = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);

            let lj = sample(d, p, l, j);
            let fj = d.apply(f, &[j]);
            let fjj = sample(d, p, fj, j);
            let bj = sample(d, p, b, j);

            // u1 : lm - lj <= modulus(m,j).
            let u1 = rsub(d, rat, head, lj);
            let b1 = modulus(d, p, m, j);
            let w1 = d.lemma(p.regular, &[l, m, j]);
            let (_, r1) = halves(d, p, u1, b1, w1);

            // u2 : lj - fjj <= K/(j+1), the NEGATED Converges witness. The
            // witness bounds `fjj - lj`; `Rat.neg_sub` rewrites its negation
            // to exactly `lj - fjj` (`u2`'s own shape, matching what
            // `telescope_le4` independently builds for this slot).
            let diff = rsub(d, rat, fjj, lj);
            let neg_diff = rneg(d, diff);
            let u2 = rsub(d, rat, lj, fjj);
            let b2 = div_succ_at(d, p, k, j);
            let w_diff = d.apply(hp, &[j]);
            let (dl, du) = halves(d, p, diff, b2, w_diff);
            let w_neg = d.lemma(rat.bounds_neg, &[diff, b2, dl, du]);
            let (_, r2_neg) = halves(d, p, neg_diff, b2, w_neg);
            let neg_sub_eq = d.lemma(rat.neg_sub, &[fjj, lj]); // Eq neg_diff u2
            let r2 = rat_eq_rewrite(d, neg_diff, u2, neg_sub_eq, r2_neg, &|d, t| {
                rle(d, rat, t, b2)
            });

            // u3 : fjj - bj <= 2/(j+1), directly from h1 at j, at index j.
            let u3 = rsub(d, rat, fjj, bj);
            let b3 = div_succ(d, p, 2, j);
            let h1_at_j = d.apply(h1, &[j]);
            let r3 = d.apply(h1_at_j, &[j]);

            // u4 : bj - bm <= modulus(j,m).
            let u4 = rsub(d, rat, bj, tail);
            let b4 = modulus(d, p, j, m);
            let w4 = d.lemma(p.regular, &[b, j, m]);
            let (_, r4) = halves(d, p, u4, b4, w4);

            let s34 = d.lemma(rat.add_le_add, &[u3, b3, u4, b4, r3, r4]);
            let q34 = radd(d, u3, u4);
            let c34 = radd(d, b3, b4);
            let s234 = d.lemma(rat.add_le_add, &[u2, b2, q34, c34, r2, s34]);
            let q234 = radd(d, u2, q34);
            let c234 = radd(d, b2, c34);
            let s1234 = d.lemma(rat.add_le_add, &[u1, b1, q234, c234, r1, s234]);
            let q1234 = radd(d, u1, q234);
            let c1234 = radd(d, b1, c234);

            let (_, _, quantity_eq) = telescope_le4(d, p, head, lj, fjj, bj, tail);
            let at_quantity = rat_eq_rewrite(d, q1234, target, quantity_eq, s1234, &|d, t| {
                rle(d, rat, t, c1234)
            });

            let (final_bound, _, bound_eq) = fuse_bridge_bound(d, p, m, j, k, two_nat);
            let moved = rat_eq_rewrite(d, c1234, final_bound, bound_eq, at_quantity, &|d, t| {
                rle(d, rat, target, t)
            });
            d.lam_fv(j_fv, nat, moved)
        };
        let k_total = bridge_total_numerator(d, k, two_nat);
        let at_index = d.lemma(
            rat.le_of_le_add_nat_div_succ,
            &[target, goal_bound, k_total, hypothesis],
        );
        let per_m = d.lam_fv(m_fv, nat, at_index);
        let with_hp = d.lam_fv(hp_fv, hp_ty, per_m);
        d.lam_fv(k_fv, nat, with_hp)
    };

    let proof_body = exists_elim(d, p, nat, predicate, target_ty, h2, minor);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, converges_fl, proof_body);
        let with_h1 = d.lam_fv(h1_fv, upper_ty, with_h2);
        let with_b = d.lam_fv(b_fv, carrier, with_h1);
        let with_l = d.lam_fv(l_fv, carrier, with_b);
        d.lam_fv(f_fv, seq_ty, with_l)
    };
    let ty = {
        let after_h2 = d.arrow(converges_fl, target_ty);
        let after_h1 = d.arrow(upper_ty, after_h2);
        let with_b = d.pi_fv(b_fv, carrier, after_h1);
        let with_l = d.pi_fv(l_fv, carrier, with_b);
        d.pi_fv(f_fv, seq_ty, with_l)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_upper_bound,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.add x y`.
fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

/// `CReal.neg x`.
fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

/// `CReal.converges_le : ∀ f g L M, Converges f L → Converges g M →
/// (∀ n, le (f n) (g n)) → le L M`.
///
/// Order passes to the limit. No new Riemann-sum or accuracy-index estimate
/// is needed here — unlike [`declare_converges_mul`]'s own obstruction (two
/// sequences sampled at *different* deep indices), the pointwise hypothesis
/// and both `Converges` witnesses are all read at the *same* index `n`, so
/// this is composition of already-proved `Converges` combinators plus
/// ordinary ring/order algebra:
///
/// 1. [`CRealPrelude::converges_sub`] applied to the two hypotheses gives
///    `Converges h (add L (neg M))`, `h n := add (f n) (neg (g n))`.
/// 2. The pointwise hypothesis `le (f n) (g n)` rearranges to `le (h n) zero`
///    via [`CRealPrelude::add_le_add`] (add `neg (g n)` to both sides) then
///    [`CRealPrelude::le_congr`] against [`CRealPrelude::add_neg`] (`g n +
///    neg (g n) ~ zero`).
/// 3. [`CRealPrelude::converges_upper_bound`] at the constant `zero` turns
///    steps 1–2 into `le (add L (neg M)) zero`.
/// 4. Adding `M` to both sides (`add_le_add` again) and cancelling
///    (`add_assoc`/`add_comm`/`add_neg`/`add_zero`, the same ring-identity
///    shape [`super::integral`]'s `add_sub_cancel`/`shift_le_of_nonneg`
///    use) recovers `le L M`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
fn declare_converges_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let converges_fl = converges_applied(d, p, f, l);
    let converges_gm = converges_applied(d, p, g, m);
    let hle_ty = le_pointwise_ty(d, p, f, g);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let neg_m = cneg(d, p, m);
    let add_l_negm = cadd(d, p, l, neg_m);

    // h_seq := fun n => add (f n) (neg (g n)).
    let h_seq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let gn_term = d.apply(g, &[n]);
        let neg_gn = cneg(d, p, gn_term);
        let body = cadd(d, p, fn_term, neg_gn);
        d.lam_fv(n_fv, nat, body)
    };

    // conv_h : Converges h_seq (add L (neg M)).
    let conv_h = d.lemma(p.converges_sub, &[f, g, l, m, h1, h2]);

    // pointwise_nonpos : forall n, le (h_seq n) zero.
    let pointwise_nonpos = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let gn_term = d.apply(g, &[n]);
        let neg_gn = cneg(d, p, gn_term);
        let hn = d.apply(hle, &[n]); // le (f n) (g n)
        let refl_neg_gn = d.lemma(p.le_refl, &[neg_gn]);
        let step = d.lemma(
            p.add_le_add,
            &[fn_term, gn_term, neg_gn, neg_gn, hn, refl_neg_gn],
        );
        // step : le (add fn neg_gn) (add gn neg_gn)
        let lhs = cadd(d, p, fn_term, neg_gn); // = h_seq n, up to beta
        let rhs = cadd(d, p, gn_term, neg_gn);
        let refl_lhs = d.lemma(p.equiv_refl, &[lhs]);
        let gn_negeq = d.lemma(p.add_neg, &[gn_term]); // Equiv (add gn neg_gn) zero
        let claim = d.lemma(
            p.le_congr,
            &[lhs, lhs, rhs, zero_c, refl_lhs, gn_negeq, step],
        );
        // claim : le lhs zero
        d.lam_fv(n_fv, nat, claim)
    };

    // le_sum_zero : le (add L (neg M)) zero.
    let le_sum_zero = d.lemma(
        p.converges_upper_bound,
        &[h_seq, add_l_negm, zero_c, pointwise_nonpos, conv_h],
    );

    // step1 : le (add add_l_negm m) (add zero m).
    let refl_m = d.lemma(p.le_refl, &[m]);
    let step1 = d.lemma(
        p.add_le_add,
        &[add_l_negm, zero_c, m, m, le_sum_zero, refl_m],
    );
    let sum_l_negm_m = cadd(d, p, add_l_negm, m);
    let zero_add_m = cadd(d, p, zero_c, m);

    // eq_l : Equiv (add add_l_negm m) L.
    let eq_l = {
        let assoc = d.lemma(p.add_assoc, &[l, neg_m, m]);
        // assoc : Equiv (add (add L neg_m) m) (add L (add neg_m m))
        let negm_m = cadd(d, p, neg_m, m);
        let m_negm = cadd(d, p, m, neg_m);
        let comm_negm_m = d.lemma(p.add_comm, &[neg_m, m]); // Equiv negm_m m_negm
        let mneg = d.lemma(p.add_neg, &[m]); // Equiv m_negm zero
        let negm_m_zero = d.lemma(p.equiv_trans, &[negm_m, m_negm, zero_c, comm_negm_m, mneg]);
        // negm_m_zero : Equiv negm_m zero
        let refl_l = d.lemma(p.equiv_refl, &[l]);
        let l_negmm = cadd(d, p, l, negm_m);
        let l_zero = cadd(d, p, l, zero_c);
        let congr1 = d.lemma(p.add_congr, &[l, l, negm_m, zero_c, refl_l, negm_m_zero]);
        // congr1 : Equiv l_negmm l_zero
        let addzero_l = d.lemma(p.add_zero, &[l]); // Equiv l_zero l
        let step_a = d.lemma(p.equiv_trans, &[l_negmm, l_zero, l, congr1, addzero_l]);
        // step_a : Equiv l_negmm l
        d.lemma(p.equiv_trans, &[sum_l_negm_m, l_negmm, l, assoc, step_a])
        // : Equiv sum_l_negm_m l
    };

    // eq_m : Equiv (add zero m) m.
    let eq_m = {
        let m_zero = cadd(d, p, m, zero_c);
        let comm_zero_m = d.lemma(p.add_comm, &[zero_c, m]); // Equiv zero_add_m m_zero
        let addzero_m = d.lemma(p.add_zero, &[m]); // Equiv m_zero m
        d.lemma(
            p.equiv_trans,
            &[zero_add_m, m_zero, m, comm_zero_m, addzero_m],
        )
    };

    let final_proof = d.lemma(
        p.le_congr,
        &[sum_l_negm_m, l, zero_add_m, m, eq_l, eq_m, step1],
    );
    // final_proof : le L M

    let concl = d.const_app(p.le, &[l, m]);
    let ty = {
        let after_hle = d.arrow(hle_ty, concl);
        let after_h2 = d.arrow(converges_gm, after_hle);
        let after_h1 = d.arrow(converges_fl, after_h2);
        let with_m = d.pi_fv(m_fv, carrier, after_h1);
        let with_l = d.pi_fv(l_fv, carrier, with_m);
        let with_g = d.pi_fv(g_fv, seq_ty, with_l);
        d.pi_fv(f_fv, seq_ty, with_g)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, final_proof);
        let with_h2 = d.lam_fv(h2_fv, converges_gm, with_hle);
        let with_h1 = d.lam_fv(h1_fv, converges_fl, with_h2);
        let with_m = d.lam_fv(m_fv, carrier, with_h1);
        let with_l = d.lam_fv(l_fv, carrier, with_m);
        let with_g = d.lam_fv(g_fv, seq_ty, with_l);
        d.lam_fv(f_fv, seq_ty, with_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_le,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
// This file is under active development; new declarations continue to land
// after this test module rather than the whole module being relocated on
// every addition. Scoped allow, not a restructuring of another lane's file.
#[allow(clippy::items_after_test_module)]
mod converges_le_tests {
    use super::*;
    use crate::Declaration;

    /// **Mandatory concrete instantiation, both directions.** `F := fun _ =>
    /// zero`, `G := fun _ => one` -- `zero != one`, so a bug that swapped `L`
    /// and `M` in `converges_le`'s conclusion is visible (unlike testing at
    /// `F = G`, where `le c c` holds regardless of which side the proof
    /// actually establishes -- see the vacuous check at the end of this test
    /// for exactly that degenerate case, kept for comparison rather than as
    /// the only check). The SAME proof term is checked against BOTH the true
    /// conclusion `le zero one` (must succeed) and the FALSE, swapped
    /// conclusion `le one zero` (must be REFUSED) -- the "inverted" control
    /// this repository's own house rule asks for, run against the exact term
    /// [`declare_converges_le`]'s construction produces, not a hand-rolled
    /// substitute.
    #[test]
    fn converges_le_concrete_and_negative_control() {
        crate::on_a_deep_stack(converges_le_concrete_and_negative_control_body);
    }

    fn converges_le_concrete_and_negative_control_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();

        let zero_c = d.kernel().const_(p.zero, vec![]);
        let one_c = d.kernel().const_(p.one, vec![]);

        let f_const_zero = {
            let ignore_fv = d.fresh_fvar();
            d.lam_fv(ignore_fv, nat, zero_c)
        };
        let g_const_one = {
            let ignore_fv = d.fresh_fvar();
            d.lam_fv(ignore_fv, nat, one_c)
        };

        let conv_f = d.lemma(p.converges_of_const, &[zero_c]);
        let conv_g = d.lemma(p.converges_of_const, &[one_c]);

        // hle : forall n, le (f_const_zero n) (g_const_one n) -- both sides
        // beta-reduce to `le zero one`, a genuine (non-vacuous) fact via
        // `zero_lt_one` + `le_of_lt`, not `le_refl` at a single point.
        let hle = {
            let n_fv = d.fresh_fvar();
            let lt01 = d.lemma(p.zero_lt_one, &[]);
            let le01 = d.lemma(p.le_of_lt, &[zero_c, one_c, lt01]);
            d.lam_fv(n_fv, nat, le01)
        };

        let proof = d.lemma(
            p.converges_le,
            &[
                f_const_zero,
                g_const_one,
                zero_c,
                one_c,
                conv_f,
                conv_g,
                hle,
            ],
        );

        let anon = d.kernel().anon();

        // Positive: the TRUE conclusion must be accepted.
        let true_ty = d.const_app(p.le, &[zero_c, one_c]);
        let name_ok = d.kernel().name_str(anon, "__convergesLeConcreteOk");
        let result_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: name_ok,
            uparams: vec![],
            ty: true_ty,
            value: proof,
        });
        assert!(
            result_ok.is_ok(),
            "converges_le at F := const zero, G := const one must prove \
             `le zero one`: {:?}",
            result_ok.err()
        );

        // Negative control: the SAME proof term, asserted at the SWAPPED
        // (false) conclusion `le one zero`, must be REFUSED.
        let false_ty = d.const_app(p.le, &[one_c, zero_c]);
        let name_bad = d.kernel().name_str(anon, "__convergesLeConcreteBad");
        let result_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_bad,
            uparams: vec![],
            ty: false_ty,
            value: proof,
        });
        assert!(
            result_bad.is_err(),
            "the SAME proof term must be REFUSED against the swapped \
             (false) conclusion `le one zero`"
        );

        // Vacuous sanity, for comparison: F = G = const zero, via `le_refl`.
        // This ALONE would not distinguish a correct proof from one that
        // silently swapped `L`/`M` -- `le zero zero` holds either way -- so
        // it is checked alongside the non-vacuous pair above, never instead
        // of it.
        let conv_f0 = d.lemma(p.converges_of_const, &[zero_c]);
        let conv_g0 = d.lemma(p.converges_of_const, &[zero_c]);
        let hle0 = {
            let n_fv = d.fresh_fvar();
            let refl0 = d.lemma(p.le_refl, &[zero_c]);
            d.lam_fv(n_fv, nat, refl0)
        };
        let proof0 = d.lemma(
            p.converges_le,
            &[
                f_const_zero,
                f_const_zero,
                zero_c,
                zero_c,
                conv_f0,
                conv_g0,
                hle0,
            ],
        );
        let vacuous_ty = d.const_app(p.le, &[zero_c, zero_c]);
        let name_vacuous = d.kernel().name_str(anon, "__convergesLeVacuous");
        let result_vacuous = d.kernel().add_declaration(Declaration::Theorem {
            name: name_vacuous,
            uparams: vec![],
            ty: vacuous_ty,
            value: proof0,
        });
        assert!(
            result_vacuous.is_ok(),
            "the degenerate F = G = const zero case must still typecheck: {:?}",
            result_vacuous.err()
        );
    }
}

// --- `CReal.Bounded`, and what it turned out to unlock ----------------------
//
// `CReal.mul`'s own regularity is a FIXED rate (see `product.rs`'s module
// documentation: the shift `mulShift x y` is chosen so the estimate closes
// with no slack), so a natural first step toward `converges_mul` is to show
// a linear-rate convergent sequence is automatically bounded — which is
// exactly [`declare_converges_bounded`] below, and it lands cleanly.
//
// An earlier account of this file read the obstruction as needing
// `CReal.bound (f n)` itself bounded uniformly in `n` — a property of `f n`'s
// representative AT INDEX 0 (`bound x := natAbs (num (seq x 0)) + 1`). That
// is not what `converges_mul`'s proof below actually needs, and is not what
// `Bounded f` supplies: `Bounded`'s witness bounds `seq (f n) n` at EACH `n`'s
// OWN index `n`, not at index `0`, so it is a different quantity from
// `CReal.bound (f n)` and the two are never equated anywhere in this
// development. What the proof needs is a bound on `seq (f n) i` for the
// PARTICULAR further index `i` that `CReal.mul`'s sampling reads `f n` at —
// and [`bounded_at_index`] gets that directly from `Bounded f`'s bound at `n`
// plus one instance of `f n`'s own regularity between `n` and `i`, with no
// detour through `CReal.bound` or `mulShift` at all.
//
// The genuine remaining obstruction was real, though: `mul (f n) (g n)` and
// `mul L M` sample their two factors at *different* deep indices
// (`mulShift (f n) (g n)` varies with `n`; `mulShift L M` is the fixed
// `bound L + bound M + 1`), so bounding, say, `seq (g n) (idx_fn_gn) −
// seq M (idx_LM)` needs a cross-index estimate between two indices *neither*
// of which is `n` — precisely the "arbitrary-third-index plus Archimedean"
// machinery `product.rs`'s own module documentation names as the reason
// `mul_assoc`/`left_distrib`/`mul_congr` needed it and
// `mul_zero`/`mul_comm`/`sq_nonneg` did not. That machinery — `product`'s
// `regular_between`, `product_gap`, `equiv_of_bounded` — was already built
// (and used by `mul_congr`/`left_distrib`/`mul_assoc`) by the time this slice
// ran; [`converges_gap_at`] is its `Converges`-hypothesis analogue, reusing
// `regular_between` rather than re-deriving it. So `Bounded`/
// `converges_bounded` ARE the piece the mul side needed — via
// [`bounded_at_index`], not via `CReal.bound` — and combined with
// `converges_gap_at` and `product_gap`, [`declare_converges_mul`] closes.

/// `∀ n, Within (seq (func n) n) (natDivSucc b 0)`, for a (possibly
/// symbolic) `Nat` bound `b`.
fn bounded_body(d: &mut IntDev<'_>, p: CRealPrelude, func: ExprId, b: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fn_term = d.apply(func, &[n]);
    let point = sample(d, p, fn_term, n);
    let zero_nat = d.num(0);
    let bound = div_succ_at(d, p, b, zero_nat);
    let claim = within(d, p, point, bound);
    d.pi_fv(n_fv, nat, claim)
}

/// `λ B, ∀ n, Within (seq (func n) n) (natDivSucc B 0)`.
fn bounded_predicate(d: &mut IntDev<'_>, p: CRealPrelude, func: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let body = bounded_body(d, p, func, b);
    d.lam_fv(b_fv, nat, body)
}

/// `CReal.Bounded func`.
fn bounded_applied(d: &mut IntDev<'_>, p: CRealPrelude, func: ExprId) -> ExprId {
    d.const_app(p.bounded, &[func])
}

/// `CReal.Bounded (g : Nat → CReal) : Prop :=
///   ∃ (B : Nat), ∀ (n : Nat), Within (seq (g n) n) (Rat.natDivSucc B 0)`.
///
/// The same canonical-sample, free-constant idiom [`declare_converges`]
/// uses, at a bound that does not even need a second point of comparison.
fn declare_bounded(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let seq_ty = seq_fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let predicate = bounded_predicate(d, p, f);
    let claim_ty = exists_ty(d, p, nat, predicate);
    let value = d.lam_fv(f_fv, seq_ty, claim_ty);
    let ty = d.arrow(seq_ty, prop);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.bounded,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 35),
    })
}

/// `CReal.bound x + 1` — the numerator [`CReal.bound_within`] bounds `seq x`
/// by, at every index. Duplicated from `product.rs`'s private
/// `magnitude_of`/`bound_value` (pure term-builders, not proofs): one call
/// site here does not carry the cost of widening a helper across a module
/// boundary.
fn bound_magnitude(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let base = d.const_app(p.bound, &[x]);
    d.succ(base)
}

/// `Rat.le (natDivSucc k j) (natDivSucc k 0)` — a numerator carries its own
/// constant bound, independent of the index.
///
/// **Not** antitonicity of `natDivSucc` in its index (the module
/// documentation is explicit that this development deliberately never
/// proves that in general). This is
/// [`Rat.natDivSucc_le_scaled`](crate::RatPrelude::nat_div_succ_le_scaled)
/// instantiated at its OWN composed index — `(k, c := j, n := 0)` — whose
/// composed form `(j+1)·0 + j` is `j` after `Nat.mul_zero`/`Nat.zero_add`.
/// The general lemma already covers indices of exactly this shape; nothing
/// new about `natDivSucc` is needed, only the two `Nat` identities that
/// collapse `(j+1)·0 + j` back to `j`.
fn nat_div_succ_le_const(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    let rat = p.rat;
    let nat = p.rat.int.nat;
    let zero_nat = d.num(0);

    // base : Rat.le (natDivSucc k ((j+1)*0+j)) (natDivSucc k 0).
    let base = d.lemma(rat.nat_div_succ_le_scaled, &[k, j, zero_nat]);

    let sj = d.succ(j);
    let scaled = NatOps::mul(d, sj, zero_nat); // (j+1)*0
    let index = NatOps::add(d, scaled, j); // (j+1)*0 + j

    let mul_zero_eq = d.lemma(nat.mul_zero, &[sj]); // Eq Nat scaled 0
    let zero_plus_j = NatOps::add(d, zero_nat, j);
    let step1 = NatOps::congr(d, scaled, zero_nat, mul_zero_eq, &|d, t| {
        NatOps::add(d, t, j)
    }); // Eq Nat index zero_plus_j

    let zero_add_eq = d.lemma(nat.zero_add, &[j]); // Eq Nat zero_plus_j j

    let (_, index_eq) = NatOps::chain(d, index, &[(zero_plus_j, step1), (j, zero_add_eq)]);

    nat_rewrite_prop(d, index, j, index_eq, base, &|d, t| {
        let deep = div_succ_at(d, p, k, t);
        let shallow = div_succ_at(d, p, k, zero_nat);
        rle(d, rat, deep, shallow)
    })
}

/// `CReal.converges_bounded : ∀ f L, Converges f L → Bounded f`.
///
/// A linear-rate convergent sequence is automatically bounded, with **no
/// choice** — the same character as [`CReal.bound_within`]'s own derivation.
/// Instantiate `Converges f L`'s witness `K` at `n`:
/// `Within (seq (f n) n − seq L n) (natDivSucc K n)`. Widen the modulus to
/// the CONSTANT `natDivSucc K 0` via [`nat_div_succ_le_const`] (not
/// antitonicity — see that helper), then combine with
/// [`CReal.bound_within`]'s own already-constant bound on `L`'s sample
/// through `Rat.bounds_add` and the identity
/// `seq L n + (seq (f n) n − seq L n) = seq (f n) n` — the same
/// `first + (point − first) = point` shape `product.rs`'s
/// `declare_bound_within` proves via one `Rat.sum_perm` plus `Rat.add_neg`/
/// `Rat.add_zero`. The witness is `(bound L + 1) + K`, reported raw.
fn declare_converges_bounded(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let nat_add = d.prelude().add;
    let zero_nat = d.num(0);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);

    let converges_fl = converges_applied(d, p, f, l);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let target = bounded_applied(d, p, f);

    let predicate = converges_predicate(d, p, f, l);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = converges_body(d, p, f, l, k);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let per_n = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);

            let fn_term = d.apply(f, &[n]);
            let a_n = sample(d, p, fn_term, n);
            let l_n = sample(d, p, l, n);
            let gap = rsub(d, rat, a_n, l_n);

            let gap_bound = div_succ_at(d, p, k, n);
            let gap_proof = d.apply(hp, &[n]);

            let wide_gap_bound = div_succ_at(d, p, k, zero_nat);
            let widen_order = nat_div_succ_le_const(d, p, k, n);
            let gap_widened = weaken(d, p, gap, gap_bound, wide_gap_bound, gap_proof, widen_order);

            let magnitude = bound_magnitude(d, p, l);
            let l_bound = div_succ_at(d, p, magnitude, zero_nat);
            let l_proof = d.lemma(p.bound_within, &[l, n]);

            let (ll, lu) = halves(d, p, l_n, l_bound, l_proof);
            let (gl, gu) = halves(d, p, gap, wide_gap_bound, gap_widened);
            let combined = d.lemma(
                rat.bounds_add,
                &[l_n, l_bound, gap, wide_gap_bound, ll, lu, gl, gu],
            );
            let total_bound = radd(d, l_bound, wide_gap_bound);

            // `l_n + (a_n − l_n) = a_n`.
            let restore = {
                let negated = rneg(d, l_n);
                let atoms = [l_n, a_n, negated];
                let sorted = [a_n, l_n, negated];
                let permute = rsum_perm(d, rat, &atoms, &sorted);
                let start = rsum(d, rat, &atoms);
                let sorted_term = rsum(d, rat, &sorted);
                let zero_rat = rzero(d, rat);
                let cancel = d.lemma(rat.add_neg, &[l_n]);
                let inner = radd(d, l_n, negated);
                let collapse = rcongr(d, inner, zero_rat, cancel, &|d, t| radd(d, a_n, t));
                let padded = radd(d, a_n, zero_rat);
                let trim = d.lemma(rat.add_zero, &[a_n]);
                let (_, proof) = rchain(
                    d,
                    start,
                    &[(sorted_term, permute), (padded, collapse), (a_n, trim)],
                );
                proof
            };
            let summed = radd(d, l_n, gap);
            let at_quantity = rat_eq_rewrite(d, summed, a_n, restore, combined, &|d, t| {
                within(d, p, t, total_bound)
            });

            let witness_b = d.const_app(nat_add, &[magnitude, k]);
            let final_bound = div_succ_at(d, p, witness_b, zero_nat);
            let fuse = d.lemma(rat.nat_div_succ_add, &[magnitude, k, zero_nat]);
            let per_n_proof =
                rat_eq_rewrite(d, total_bound, final_bound, fuse, at_quantity, &|d, t| {
                    within(d, p, a_n, t)
                });

            (n_fv, witness_b, per_n_proof)
        };

        let (n_fv, witness_b, per_n_proof) = per_n;
        let per_n_lam = d.lam_fv(n_fv, nat, per_n_proof);
        let bounded_pred = bounded_predicate(d, p, f);
        let witnessed = exists_intro(d, p, nat, bounded_pred, witness_b, per_n_lam);

        let with_hp = d.lam_fv(hp_fv, hp_ty, witnessed);
        d.lam_fv(k_fv, nat, with_hp)
    };

    let proof_body = exists_elim(d, p, nat, predicate, target, h, minor);

    let value = {
        let with_h = d.lam_fv(h_fv, converges_fl, proof_body);
        let with_l = d.lam_fv(l_fv, carrier, with_h);
        d.lam_fv(f_fv, seq_ty, with_l)
    };
    let ty = {
        let after_h = d.arrow(converges_fl, target);
        let with_l = d.pi_fv(l_fv, carrier, after_h);
        d.pi_fv(f_fv, seq_ty, with_l)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_bounded,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.converges_mul` --------------------------------------------------
//
// See the module documentation for the obstruction (`CReal.mul`'s two
// per-`n` VARIABLE shifts) and its resolution. Two reusable pieces close it:
//
// [`bounded_at_index`] widens `Bounded f`'s bound — stated only at each `n`'s
// OWN sample, `Within (seq (f n) n) (B/1)` — to a bound uniform in BOTH `n`
// and an arbitrary further index, by the same triangle-inequality shape
// [`product::declare_bound_within`] proves from the DEFINITIONAL bound at
// index `0` (`|u_i| ≤ |u_anchor| + |u_i − u_anchor| ≤ B + 2`), generalised to
// an arbitrary anchor because `Bounded`'s witness lives at `n`, not at `0`.
//
// [`converges_gap_at`] is the cross-index, cross-real estimate
// `product.rs`'s own module documentation named as the reason `mul_assoc`/
// `left_distrib`/`mul_congr` needed machinery this development did not have:
// telescope `u_high − v_low = (u_high − u_n) + (u_n − v_n) + (v_n − v_low)`,
// bound the outer two terms by [`product::regular_between`] (REUSED, not
// re-derived — the same helper `mul_congr`'s `cross_gap` already runs on),
// and the middle term by the `Converges` hypothesis directly — no widening
// needed there, since it is already stated at `n`.
//
// Only ONE boundedness fact is needed, not two: `Rat.mul_sub_mul`'s
// asymmetric split (`a·b − c·e = a·(b−e) + (a−c)·e`) bounds a factor of the
// LEFT product (`a`, from `f`) and a factor of the RIGHT one (`e`, from `M`,
// a FIXED real that already has `CReal.bound_within`) — `b` and `c` are never
// bounded on their own, only inside the two gap differences. So
// [`declare_converges_bounded`] supplies exactly the one fact this needed,
// and [`product::product_gap`] (REUSED exactly as `mul_congr`/`left_distrib`
// use it) closes the combination.

/// `Within (seq u i) (natDivSucc (b + 2) 0)`, and the numerator `b + 2`,
/// given a uniform `Nat` bound `b` on `u`'s OWN sample at some anchor index
/// (`anchor_proof : Within (seq u anchor) (natDivSucc b 0)`).
fn bounded_at_index(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    anchor: ExprId,
    b: ExprId,
    anchor_proof: ExprId,
    i: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let zero_nat = d.num(0);

    let first = sample(d, p, u, anchor);
    let point = sample(d, p, u, i);
    let base = div_succ_at(d, p, b, zero_nat);
    let gap = rsub(d, rat, point, first);
    let spread = modulus(d, p, i, anchor);
    let regular = d.lemma(p.regular, &[u, i, anchor]);
    let (gap_low, gap_high) = halves(d, p, gap, spread, regular);
    let (anchor_low, anchor_high) = halves(d, p, first, base, anchor_proof);
    let combined = d.lemma(
        rat.bounds_add,
        &[
            first,
            base,
            gap,
            spread,
            anchor_low,
            anchor_high,
            gap_low,
            gap_high,
        ],
    );
    let total_bound = radd(d, base, spread);

    // `u_anchor + (u_i − u_anchor) = u_i`.
    let restore = {
        let negated = rneg(d, first);
        let atoms = [first, point, negated];
        let sorted = [point, first, negated];
        let permute = rsum_perm(d, rat, &atoms, &sorted);
        let start = rsum(d, rat, &atoms);
        let sorted_term = rsum(d, rat, &sorted);
        let zero_rat = rzero(d, rat);
        let cancel = d.lemma(rat.add_neg, &[first]);
        let inner = radd(d, first, negated);
        let collapse = rcongr(d, inner, zero_rat, cancel, &|d, t| radd(d, point, t));
        let padded = radd(d, point, zero_rat);
        let trim = d.lemma(rat.add_zero, &[point]);
        let (_, proof) = rchain(
            d,
            start,
            &[(sorted_term, permute), (padded, collapse), (point, trim)],
        );
        proof
    };
    let summed = radd(d, first, gap);
    let at_quantity = rat_eq_rewrite(d, summed, point, restore, combined, &|d, t| {
        within(d, p, t, total_bound)
    });

    // `1/(i+1) + 1/(anchor+1) ≤ 1/1 + 1/1 = 2/1` — BOTH legs need
    // `Rat.natDivSucc_le_one` here (unlike `product::declare_bound_within`,
    // whose anchor is the literal `0`, so its second leg is already `1/1`).
    let unit = div_succ(d, p, 1, zero_nat);
    let deep_i = div_succ(d, p, 1, i);
    let deep_anchor = div_succ(d, p, 1, anchor);
    let le_i = d.lemma(rat.nat_div_succ_le_one, &[i]);
    let le_anchor = d.lemma(rat.nat_div_succ_le_one, &[anchor]);
    let widened = d.lemma(
        rat.add_le_add,
        &[deep_i, unit, deep_anchor, unit, le_i, le_anchor],
    );
    let doubled = radd(d, unit, unit);
    let two_unit = div_succ(d, p, 2, zero_nat);
    let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, zero_nat]);
    let spread_le = rat_eq_rewrite(d, doubled, two_unit, fuse, widened, &|d, t| {
        rle(d, rat, spread, t)
    });
    let base_refl = d.lemma(rat.le_refl, &[base]);
    let grown = d.lemma(
        rat.add_le_add,
        &[base, base, spread, two_unit, base_refl, spread_le],
    );
    let padded_bound = radd(d, base, two_unit);
    let numerator = NatOps::add(d, b, two_nat);
    let target = div_succ_at(d, p, numerator, zero_nat);
    let fuse_bound = d.lemma(rat.nat_div_succ_add, &[b, two_nat, zero_nat]);
    let order = rat_eq_rewrite(d, padded_bound, target, fuse_bound, grown, &|d, t| {
        rle(d, rat, total_bound, t)
    });
    let proof = weaken(d, p, point, total_bound, target, at_quantity, order);
    (numerator, proof)
}

/// `Within (seq u high − seq v low) (natDivSucc ((2+k)+2) n)`, and the
/// numerator `(2+k)+2`, from a `Converges`-shaped bound `hyp_at_n : Within
/// (seq u n − seq v n) (natDivSucc k n)` and index proofs that `high`/`low`
/// are no shallower than `n` (`Rat.le (natDivSucc 1 high) (natDivSucc 1 n)`,
/// likewise for `low`).
///
/// The `Converges` analogue of [`product::cross_gap`] (which does the same
/// telescope from an `Equiv` hypothesis): `u_high − v_low = (u_high − u_n) +
/// (u_n − v_n) + (v_n − v_low)`, the outer two terms by
/// [`product::regular_between`] and the middle one by `hyp_at_n` directly.
fn converges_gap_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    high: ExprId,
    low: ExprId,
    high_le: ExprId,
    low_le: ExprId,
    n: ExprId,
    k: ExprId,
    hyp_at_n: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let two_nat = d.num(2);

    let n_le = {
        let one_n = div_succ(d, p, 1, n);
        d.lemma(rat.le_refl, &[one_n])
    };

    let a = sample(d, p, u, high);
    let b = sample(d, p, u, n);
    let c = sample(d, p, v, n);
    let e = sample(d, p, v, low);

    let t1 = regular_between(d, p, u, high, n, high_le, n_le, n);
    let t2 = hyp_at_n;
    let t3 = regular_between(d, p, v, n, low, n_le, low_le, n);

    let ab = rsub(d, rat, a, b);
    let bc = rsub(d, rat, b, c);
    let ce = rsub(d, rat, c, e);

    let first_two = fuse_at(d, p, ab, two_nat, bc, k, n, t1, t2);
    let inner_numerator = NatOps::add(d, two_nat, k);
    let fuse1 = d.lemma(rat.sub_add_sub, &[a, b, c]); // Eq (ab+bc) (a-c)
    let ac = rsub(d, rat, a, c);
    let inner_bound = div_succ_at(d, p, inner_numerator, n);
    let ab_bc = radd(d, ab, bc);
    let at_ac = rat_eq_rewrite(d, ab_bc, ac, fuse1, first_two, &|d, t| {
        within(d, p, t, inner_bound)
    });

    let combined = fuse_at(d, p, ac, inner_numerator, ce, two_nat, n, at_ac, t3);
    let final_numerator = NatOps::add(d, inner_numerator, two_nat);
    let fuse2 = d.lemma(rat.sub_add_sub, &[a, c, e]); // Eq (ac+ce) (a-e)
    let ae = rsub(d, rat, a, e);
    let final_bound = div_succ_at(d, p, final_numerator, n);
    let ac_ce = radd(d, ac, ce);
    let proof = rat_eq_rewrite(d, ac_ce, ae, fuse2, combined, &|d, t| {
        within(d, p, t, final_bound)
    });
    (final_numerator, proof)
}

/// `CReal.converges_mul : ∀ f g L M, Converges f L → Converges g M →
/// Converges (fun n => mul (f n) (g n)) (mul L M)`.
///
/// See the module documentation immediately above for the two reusable
/// pieces this needed (`bounded_at_index`, `converges_gap_at`) and why only
/// `Bounded f`, not `Bounded g`, is required. The witness is raw:
/// `(Bf+2)·((2+K₂)+2) + (bound M + 1)·((2+K₁)+2)`.
fn declare_converges_mul(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let one_nat = d.num(1);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let fg = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let gn_term = d.apply(g, &[n]);
        let product = cmul(d, p, fn_term, gn_term);
        d.lam_fv(n_fv, nat, product)
    };
    let mul_lm = cmul(d, p, l, m);

    let converges_fl = converges_applied(d, p, f, l);
    let converges_gm = converges_applied(d, p, g, m);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let target = converges_applied(d, p, fg, mul_lm);

    let outer_predicate = converges_predicate(d, p, f, l);
    let outer_minor = {
        let k1_fv = d.fresh_fvar();
        let k1 = d.kernel().fvar(k1_fv);
        let hp1_ty = converges_body(d, p, f, l, k1);
        let hp1_fv = d.fresh_fvar();
        let hp1 = d.kernel().fvar(hp1_fv);

        let inner_predicate = converges_predicate(d, p, g, m);
        let inner_minor = {
            let k2_fv = d.fresh_fvar();
            let k2 = d.kernel().fvar(k2_fv);
            let hp2_ty = converges_body(d, p, g, m, k2);
            let hp2_fv = d.fresh_fvar();
            let hp2 = d.kernel().fvar(hp2_fv);

            // `Bounded f`, from `Converges f L` — the one boundedness fact
            // this needs (see the module documentation above).
            let bounded_f = d.lemma(p.converges_bounded, &[f, l, h1]);
            let bounded_pred = bounded_predicate(d, p, f);
            let bounded_minor = {
                let b_fv = d.fresh_fvar();
                let b = d.kernel().fvar(b_fv);
                let hb_ty = bounded_body(d, p, f, b);
                let hb_fv = d.fresh_fvar();
                let hb = d.kernel().fvar(hb_fv);

                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);

                let fn_term = d.apply(f, &[n]);
                let gn_term = d.apply(g, &[n]);

                let c1 = mul_shift(d, p, fn_term, gn_term);
                let c2 = mul_shift(d, p, l, m);
                let idx1 = mul_index(d, c1, n);
                let idx2 = mul_index(d, c2, n);

                let idx1_le = index_le(d, p, one_nat, c1, n);
                let idx2_le = index_le(d, p, one_nat, c2, n);

                let hp1_n = d.apply(hp1, &[n]);
                let hp2_n = d.apply(hp2, &[n]);

                let (g1, gap_be) =
                    converges_gap_at(d, p, gn_term, m, idx1, idx2, idx1_le, idx2_le, n, k2, hp2_n);
                let (g2, gap_ac) =
                    converges_gap_at(d, p, fn_term, l, idx1, idx2, idx1_le, idx2_le, n, k1, hp1_n);

                let a = sample(d, p, fn_term, idx1);
                let bb = sample(d, p, gn_term, idx1);
                let cc = sample(d, p, l, idx2);
                let e = sample(d, p, m, idx2);

                let hb_n = d.apply(hb, &[n]);
                let (ka, a_bound) = bounded_at_index(d, p, fn_term, n, b, hb_n, idx1);

                let e_bound = d.lemma(p.bound_within, &[m, idx2]);
                let ke = bound_magnitude(d, p, m);

                let at_n = product_gap(
                    d, p, a, bb, cc, e, ka, ke, g1, g2, n, a_bound, e_bound, gap_be, gap_ac,
                );

                let k_total = {
                    let head = NatOps::mul(d, ka, g1);
                    let tail = NatOps::mul(d, ke, g2);
                    NatOps::add(d, head, tail)
                };

                let per_n_lam = d.lam_fv(n_fv, nat, at_n);
                let converges_pred = converges_predicate(d, p, fg, mul_lm);
                let witnessed = exists_intro(d, p, nat, converges_pred, k_total, per_n_lam);

                let with_hb = d.lam_fv(hb_fv, hb_ty, witnessed);
                d.lam_fv(b_fv, nat, with_hb)
            };
            let bounded_elim =
                exists_elim(d, p, nat, bounded_pred, target, bounded_f, bounded_minor);

            let with_hp2 = d.lam_fv(hp2_fv, hp2_ty, bounded_elim);
            d.lam_fv(k2_fv, nat, with_hp2)
        };
        let inner_elim = exists_elim(d, p, nat, inner_predicate, target, h2, inner_minor);

        let with_hp1 = d.lam_fv(hp1_fv, hp1_ty, inner_elim);
        d.lam_fv(k1_fv, nat, with_hp1)
    };
    let proof_body = exists_elim(d, p, nat, outer_predicate, target, h1, outer_minor);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, converges_gm, proof_body);
        let with_h1 = d.lam_fv(h1_fv, converges_fl, with_h2);
        let with_m = d.lam_fv(m_fv, carrier, with_h1);
        let with_l = d.lam_fv(l_fv, carrier, with_m);
        let with_g = d.lam_fv(g_fv, seq_ty, with_l);
        d.lam_fv(f_fv, seq_ty, with_g)
    };
    let ty = {
        let after_h2 = d.arrow(converges_gm, target);
        let after_h1 = d.arrow(converges_fl, after_h2);
        let with_m = d.pi_fv(m_fv, carrier, after_h1);
        let with_l = d.pi_fv(l_fv, carrier, with_m);
        let with_g = d.pi_fv(g_fv, seq_ty, with_l);
        d.pi_fv(f_fv, seq_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_mul,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.ContinuousAt` (sequential form) ---------------------------------

/// `CReal → CReal`.
fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

/// `λ n, func (g n)` — the composed sequence `func ∘ g`.
fn compose_seq(d: &mut IntDev<'_>, _p: CRealPrelude, func: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let gn = d.apply(g, &[n]);
    let applied = d.apply(func, &[gn]);
    d.lam_fv(n_fv, nat, applied)
}

/// `∀ (g : Nat → CReal), Converges g x → Converges (fun n => func (g n)) (func x)`.
fn continuous_at_body(d: &mut IntDev<'_>, p: CRealPrelude, func: ExprId, x: ExprId) -> ExprId {
    let seq_ty = seq_fn_ty(d, p);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let converges_gx = converges_applied(d, p, g, x);
    let composed = compose_seq(d, p, func, g);
    let fx = d.apply(func, &[x]);
    let target = converges_applied(d, p, composed, fx);
    let body = d.arrow(converges_gx, target);
    d.pi_fv(g_fv, seq_ty, body)
}

/// `CReal.ContinuousAt func x`.
fn continuous_at_applied(d: &mut IntDev<'_>, p: CRealPrelude, func: ExprId, x: ExprId) -> ExprId {
    d.const_app(p.continuous_at, &[func, x])
}

/// `CReal.ContinuousAt (F : CReal → CReal) (x : CReal) : Prop :=
///   ∀ (g : Nat → CReal), Converges g x → Converges (fun n => F (g n)) (F x)`.
///
/// **Sequential continuity**, phrased entirely through
/// [`CReal.Converges`](CRealPrelude::converges) rather than a new modulus —
/// mirroring the existing convention instead of inventing a second one, per
/// the task brief. This is the standard constructive reading of continuity
/// at a point: `F` preserves every sequence converging to `x`. It costs no
/// new rational-algebra estimate at all — the two anchors and the sum law
/// below are pure applications of theorems this module already has.
fn declare_continuous_at(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let prop = d.kernel().sort_zero();
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let body = continuous_at_body(d, p, f, x);
    let value = {
        let with_x = d.lam_fv(x_fv, carrier, body);
        d.lam_fv(f_fv, func_ty, with_x)
    };
    let ty = {
        let inner = d.arrow(carrier, prop);
        d.arrow(func_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuous_at,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 36),
    })
}

/// `CReal.continuous_id : ∀ x, ContinuousAt (fun r => r) x`.
///
/// The cheapest anchor: `fun n => (fun r => r) (g n)` is `g` itself up to
/// beta and Pi-eta (`tc.rs`'s module documentation lists eta-expansion as
/// in scope), so the hypothesis `Converges g x` already **is** a proof of
/// the stated conclusion — no rational algebra at all.
fn declare_continuous_id(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let converges_gx = converges_applied(d, p, g, x);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let value = {
        let with_h = d.lam_fv(h_fv, converges_gx, h);
        let with_g = d.lam_fv(g_fv, seq_ty, with_h);
        d.lam_fv(x_fv, carrier, with_g)
    };
    let ty = {
        let applied = continuous_at_applied(d, p, identity, x);
        d.pi_fv(x_fv, carrier, applied)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.continuous_id,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.continuous_const : ∀ c x, ContinuousAt (fun _ => c) x`.
///
/// The second cheap anchor: `fun n => (fun _ => c) (g n)` beta-reduces to
/// `fun n => c`, so the target is exactly `Converges (fun n => c) c`, which
/// is [`CReal.converges_of_const`](CRealPrelude::converges_of_const) — the
/// `g`/hypothesis pair is not even used.
fn declare_continuous_const(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let const_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, c)
    };

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let converges_gx = converges_applied(d, p, g, x);
    let h_fv = d.fresh_fvar();

    let proof = d.lemma(p.converges_of_const, &[c]);

    let value = {
        let with_h = d.lam_fv(h_fv, converges_gx, proof);
        let with_g = d.lam_fv(g_fv, seq_ty, with_h);
        let with_x = d.lam_fv(x_fv, carrier, with_g);
        d.lam_fv(c_fv, carrier, with_x)
    };
    let ty = {
        let applied = continuous_at_applied(d, p, const_fn, x);
        let with_x = d.pi_fv(x_fv, carrier, applied);
        d.pi_fv(c_fv, carrier, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.continuous_const,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.continuous_add : ∀ F G x, ContinuousAt F x → ContinuousAt G x →
///   ContinuousAt (fun r => add (F r) (G r)) x`.
///
/// Closure under sums, transferred straight from
/// [`CReal.converges_add`](CRealPrelude::converges_add): given `g` converging
/// to `x`, `hF g h` and `hG g h` give `Converges (fun n => F (g n)) (F x)`
/// and `Converges (fun n => G (g n)) (G x)`, and `converges_add` combines
/// them into exactly the (beta-equal) target. No new estimate.
fn declare_continuous_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let func_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let big_g_fv = d.fresh_fvar();
    let big_g = d.kernel().fvar(big_g_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let sum_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(big_g, &[r]);
        let added = d.const_app(p.add, &[fr, gr]);
        d.lam_fv(r_fv, carrier, added)
    };

    let continuous_f = continuous_at_applied(d, p, f, x);
    let continuous_g = continuous_at_applied(d, p, big_g, x);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let converges_gx = converges_applied(d, p, g, x);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hf_applied = d.apply(hf, &[g, h]);
    let hg_applied = d.apply(hg, &[g, h]);

    let composed_f = compose_seq(d, p, f, g);
    let composed_g = compose_seq(d, p, big_g, g);
    let fx = d.apply(f, &[x]);
    let gx = d.apply(big_g, &[x]);

    let combined = d.lemma(
        p.converges_add,
        &[composed_f, composed_g, fx, gx, hf_applied, hg_applied],
    );

    let value = {
        let with_h = d.lam_fv(h_fv, converges_gx, combined);
        let with_g = d.lam_fv(g_fv, seq_ty, with_h);
        let with_hg = d.lam_fv(hg_fv, continuous_g, with_g);
        let with_hf = d.lam_fv(hf_fv, continuous_f, with_hg);
        let with_x = d.lam_fv(x_fv, carrier, with_hf);
        let with_big_g = d.lam_fv(big_g_fv, func_ty, with_x);
        d.lam_fv(f_fv, func_ty, with_big_g)
    };
    let ty = {
        let applied = continuous_at_applied(d, p, sum_fn, x);
        let after_hg = d.arrow(continuous_g, applied);
        let after_hf = d.arrow(continuous_f, after_hg);
        let with_x = d.pi_fv(x_fv, carrier, after_hf);
        let with_big_g = d.pi_fv(big_g_fv, func_ty, with_x);
        d.pi_fv(f_fv, func_ty, with_big_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.continuous_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.continuous_mul : ∀ F G x, ContinuousAt F x → ContinuousAt G x →
///   ContinuousAt (fun r => mul (F r) (G r)) x`.
///
/// Closure under products, transferred straight from
/// [`CReal.converges_mul`](CRealPrelude::converges_mul) exactly as
/// [`declare_continuous_add`] transfers `converges_add`: given `g`
/// converging to `x`, `hF g h` and `hG g h` give `Converges (fun n => F (g
/// n)) (F x)` and `Converges (fun n => G (g n)) (G x)`, and `converges_mul`
/// combines them into the (beta-equal) target. No new estimate — the
/// arbitrary-third-index machinery `converges_mul` itself needed is entirely
/// hidden behind that one lemma call.
fn declare_continuous_mul(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let func_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let big_g_fv = d.fresh_fvar();
    let big_g = d.kernel().fvar(big_g_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let prod_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(big_g, &[r]);
        let multiplied = cmul(d, p, fr, gr);
        d.lam_fv(r_fv, carrier, multiplied)
    };

    let continuous_f = continuous_at_applied(d, p, f, x);
    let continuous_g = continuous_at_applied(d, p, big_g, x);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let converges_gx = converges_applied(d, p, g, x);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hf_applied = d.apply(hf, &[g, h]);
    let hg_applied = d.apply(hg, &[g, h]);

    let composed_f = compose_seq(d, p, f, g);
    let composed_g = compose_seq(d, p, big_g, g);
    let fx = d.apply(f, &[x]);
    let gx = d.apply(big_g, &[x]);

    let combined = d.lemma(
        p.converges_mul,
        &[composed_f, composed_g, fx, gx, hf_applied, hg_applied],
    );

    let value = {
        let with_h = d.lam_fv(h_fv, converges_gx, combined);
        let with_g = d.lam_fv(g_fv, seq_ty, with_h);
        let with_hg = d.lam_fv(hg_fv, continuous_g, with_g);
        let with_hf = d.lam_fv(hf_fv, continuous_f, with_hg);
        let with_x = d.lam_fv(x_fv, carrier, with_hf);
        let with_big_g = d.lam_fv(big_g_fv, func_ty, with_x);
        d.lam_fv(f_fv, func_ty, with_big_g)
    };
    let ty = {
        let applied = continuous_at_applied(d, p, prod_fn, x);
        let after_hg = d.arrow(continuous_g, applied);
        let after_hf = d.arrow(continuous_f, after_hg);
        let with_x = d.pi_fv(x_fv, carrier, after_hf);
        let with_big_g = d.pi_fv(big_g_fv, func_ty, with_x);
        d.pi_fv(f_fv, func_ty, with_big_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.continuous_mul,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.continuous_comp : ∀ F G x, ContinuousAt F x → ContinuousAt G (F x)
///   → ContinuousAt (fun r => G (F r)) x`.
///
/// Composition. For `g` converging to `x`, `hF g h : Converges (fun n => F
/// (g n)) (F x)` — call this sequence `composed_f`, converging to `F x`.
/// Applying `hG` (continuity of `G` **at `F x`**, not at `x`) to
/// `composed_f` and `hF g h` gives `Converges (fun n => G (composed_f n))
/// (G (F x))`, which is exactly the target `Converges (fun n => (G∘F) (g
/// n)) ((G∘F) x)` up to beta. No modulus chases a shift here either: this
/// composes two existing sequential witnesses rather than building a new
/// rational estimate.
fn declare_continuous_comp(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let func_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let big_g_fv = d.fresh_fvar();
    let big_g = d.kernel().fvar(big_g_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let fx = d.apply(f, &[x]);

    let comp_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gfr = d.apply(big_g, &[fr]);
        d.lam_fv(r_fv, carrier, gfr)
    };

    let continuous_f = continuous_at_applied(d, p, f, x);
    let continuous_g = continuous_at_applied(d, p, big_g, fx);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let converges_gx = converges_applied(d, p, g, x);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // `hf_applied : Converges (fun n => f (g n)) (f x)`.
    let hf_applied = d.apply(hf, &[g, h]);
    let composed_f = compose_seq(d, p, f, g);
    // `hg_applied : Converges (fun n => big_g (composed_f n)) (big_g fx)`.
    let hg_applied = d.apply(hg, &[composed_f, hf_applied]);

    let value = {
        let with_h = d.lam_fv(h_fv, converges_gx, hg_applied);
        let with_g = d.lam_fv(g_fv, seq_ty, with_h);
        let with_hg = d.lam_fv(hg_fv, continuous_g, with_g);
        let with_hf = d.lam_fv(hf_fv, continuous_f, with_hg);
        let with_x = d.lam_fv(x_fv, carrier, with_hf);
        let with_big_g = d.lam_fv(big_g_fv, func_ty, with_x);
        d.lam_fv(f_fv, func_ty, with_big_g)
    };
    let ty = {
        let applied = continuous_at_applied(d, p, comp_fn, x);
        let after_hg = d.arrow(continuous_g, applied);
        let after_hf = d.arrow(continuous_f, after_hg);
        let with_x = d.pi_fv(x_fv, carrier, after_hf);
        let with_big_g = d.pi_fv(big_g_fv, func_ty, with_x);
        d.pi_fv(f_fv, func_ty, with_big_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.continuous_comp,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.converges_comp_eventually` --------------------------------------
//
// See `docs/mathematics-2026-08/diary-exact-root-obstruction.md`'s final
// section: the naive `Converges f L → UniformlyContinuousOn F a b →
// Converges (F ∘ f) (F L)` is FALSE here, because `UniformlyContinuousOn`'s
// `modulus : Nat → Nat` carries no growth bound and `Converges` states a
// FIXED `O(1/n)` rate. The true statement is eventual: for each accuracy
// `e`, `N := succ(K'·(modulus e) + K')` — one more than
// `Rat.natDivSucc_scale`'s own `(c+1)·m+c` index at `c := K'` — works, and
// nothing about `modulus` is ever inverted or searched.
//
// The conclusion is stated in `close_within` form (the shape
// `UniformlyContinuousOn.spec` itself produces — this file's own private
// copy, mirroring `uniform_continuity.rs`/`integral.rs`'s), not `Within`
// (the shape `Converges` uses): the spec application is a one-step consumer
// of exactly `close_within`, and wrapping the result back into `Within`
// would need a *second* real-to-rational bridge this file does not need
// otherwise.

/// `CReal.le (CReal.abs (CReal.add x (CReal.neg y))) (CReal.ofRat q)` —
/// `|x − y| ≤ q`, real-valued and index-free in `x, y`. A private copy of
/// `uniform_continuity.rs`/`integral.rs`'s own `close_within` (Rust privacy:
/// each is a sibling module, so none sees another's `fn`).
fn close_within(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, q: ExprId) -> ExprId {
    let ny = d.const_app(p.neg, &[y]);
    let diff = d.const_app(p.add, &[x, ny]);
    let magnitude = d.const_app(p.abs, &[diff]);
    let target = d.const_app(p.of_rat, &[q]);
    d.const_app(p.le, &[magnitude, target])
}

/// `λ N, ∀ n, Nat.le N n → close_within (F (f n)) (F L) (natDivSucc 1 e)`.
fn comp_predicate(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f_big: ExprId,
    f: ExprId,
    l: ExprId,
    e: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let big_n_fv = d.fresh_fvar();
    let big_n = d.kernel().fvar(big_n_fv);
    let body = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let hn_ty = d.le(big_n, n);
        let fn_term = d.apply(f, &[n]);
        let f_fn = d.apply(f_big, &[fn_term]);
        let f_l = d.apply(f_big, &[l]);
        let one_nat = d.num(1);
        let out_bound = div_succ_at(d, p, one_nat, e);
        let concl = close_within(d, p, f_fn, f_l, out_bound);
        let inner = d.arrow(hn_ty, concl);
        d.pi_fv(n_fv, nat, inner)
    };
    d.lam_fv(big_n_fv, nat, body)
}

/// `Exists Nat (comp_predicate F f L e)`.
fn comp_conclusion_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f_big: ExprId,
    f: ExprId,
    l: ExprId,
    e: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let pred = comp_predicate(d, p, f_big, f, l, e);
    exists_ty(d, p, nat, pred)
}

/// `Eq ((b+c)+(-c)) b` — adding then subtracting the same rational cancels.
fn add_sub_cancel(d: &mut IntDev<'_>, p: CRealPrelude, b: ExprId, c: ExprId) -> (ExprId, ExprId) {
    let rat = p.rat;
    let bc = radd(d, b, c);
    let neg_c = rneg(d, c);
    let lhs = radd(d, bc, neg_c);
    let c_plus_negc = radd(d, c, neg_c);
    let assoc = d.lemma(rat.add_assoc, &[b, c, neg_c]); // Eq lhs (b+(c+(-c)))
    let staged = radd(d, b, c_plus_negc);
    let zero = rzero(d, rat);
    let add_neg_proof = d.lemma(rat.add_neg, &[c]); // Eq (c+(-c)) zero
    let cancel = rcongr(d, c_plus_negc, zero, add_neg_proof, &|d, t| radd(d, b, t));
    let b_plus_zero = radd(d, b, zero);
    let add_zero_proof = d.lemma(rat.add_zero, &[b]); // Eq (b+0) b
    let (_, proof) = rchain(
        d,
        lhs,
        &[(staged, assoc), (b_plus_zero, cancel), (b, add_zero_proof)],
    );
    (b, proof)
}

/// `Rat.le (natDivSucc 2 (shift mm)) (natDivSucc 2 mm)` — `half_shift_le`
/// doubled via `Rat.add_le_add` and refused back into a single `natDivSucc`
/// by `Rat.natDivSucc_add`.
fn doubled_half_shift_le(d: &mut IntDev<'_>, p: CRealPrelude, mm: ExprId) -> ExprId {
    let rat = p.rat;
    let smm = shift(d, mm);
    let one_sm = div_succ(d, p, 1, smm);
    let one_m = div_succ(d, p, 1, mm);
    let half = half_shift_le(d, p, mm);
    let doubled = d.lemma(rat.add_le_add, &[one_sm, one_m, one_sm, one_m, half, half]);
    let sum_sm = radd(d, one_sm, one_sm);
    let sum_m = radd(d, one_m, one_m);
    let two_sm = div_succ(d, p, 2, smm);
    let two_m = div_succ(d, p, 2, mm);
    let one_nat = d.num(1);
    let fuse_sm = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, smm]);
    let fuse_m = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, mm]);
    let step1 = rat_eq_rewrite(d, sum_sm, two_sm, fuse_sm, doubled, &|d, t| {
        rle(d, rat, t, sum_m)
    });
    rat_eq_rewrite(d, sum_m, two_m, fuse_m, step1, &|d, t| {
        rle(d, rat, two_sm, t)
    })
}

/// For `mm : Nat`, `Rat.le (rsub (rsub (sample u (shift mm)) (sample v
/// (shift mm))) (natDivSucc k_total n)) (natDivSucc 2 mm)`, given `upper_uv
/// : Rat.le (rsub (sample u n) (sample v n)) (natDivSucc k n)` — the shared
/// telescope both `abs_le` premises of
/// [`close_within_of_sample_bound`] reduce to (`(u,v) := (x,y)` for the
/// direct one, `(u,v) := (y,x)` for the negated one). Bridges `u`'s and
/// `v`'s own regularity between `n` and `shift mm` (`CReal.regular`, a
/// `1/(mm+1)`-flavoured cost each way), reuses `upper_uv` directly as the
/// telescope's own middle term (padded with one trivial zero-width step to
/// match [`telescope_le4`]'s four-step shape and [`fuse_bridge_bound`]'s
/// four-piece fusion), and discharges the shift's own residual via
/// [`doubled_half_shift_le`] — no Archimedean squeeze, since `shift mm` is a
/// deterministic function of the very `mm` the goal is already universal in.
///
/// Returns `(k_total, proof)`, `k_total` from [`fuse_bridge_bound`]'s own
/// numerator so the caller can build the matching `natDivSucc k_total n`
/// bound without re-deriving it.
fn shifted_bound_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    n: ExprId,
    k: ExprId,
    upper_uv: ExprId,
    mm: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let smm = shift(d, mm);
    let head = sample(d, p, u, smm);
    let p1 = sample(d, p, u, n);
    let p2 = sample(d, p, v, n);
    let p3 = p2;
    let tail = sample(d, p, v, smm);
    let zero_nat = d.num(0);

    // r1 : (head - p1) <= modulus(smm, n).
    let b1 = modulus(d, p, smm, n);
    let u1 = rsub(d, rat, head, p1);
    let w1 = d.lemma(p.regular, &[u, smm, n]);
    let (_, r1) = halves(d, p, u1, b1, w1);

    // r2 = upper_uv : (p1 - p2) <= natDivSucc k n.
    let b2 = div_succ_at(d, p, k, n);
    let u2 = rsub(d, rat, p1, p2);

    // r3 : (p2 - p3) <= natDivSucc 0 n -- p3 = p2, a trivial zero step, only
    // present so this telescope matches `telescope_le4`/`fuse_bridge_bound`'s
    // four-piece shape.
    let b3 = div_succ_at(d, p, zero_nat, n);
    let u3 = rsub(d, rat, p2, p3);
    let r3 = {
        let zero = rzero(d, rat);
        let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[zero_nat, n]);
        let self_eq = d.lemma(rat.sub_self, &[p2]); // Eq u3 zero
        let flip = rsymm(d, u3, zero, self_eq); // Eq zero u3
        rat_eq_rewrite(d, zero, u3, flip, nonneg, &|d, t| rle(d, rat, t, b3))
    };

    // r4 : (p3 - tail) <= modulus(n, smm).
    let b4 = modulus(d, p, n, smm);
    let u4 = rsub(d, rat, p3, tail);
    let w4 = d.lemma(p.regular, &[v, n, smm]);
    let (_, r4) = halves(d, p, u4, b4, w4);

    let s34 = d.lemma(rat.add_le_add, &[u3, b3, u4, b4, r3, r4]);
    let q34 = radd(d, u3, u4);
    let c34 = radd(d, b3, b4);
    let s234 = d.lemma(rat.add_le_add, &[u2, b2, q34, c34, upper_uv, s34]);
    let q234 = radd(d, u2, q34);
    let c234 = radd(d, b2, c34);
    let s1234 = d.lemma(rat.add_le_add, &[u1, b1, q234, c234, r1, s234]);
    let q1234 = radd(d, u1, q234);
    let c1234 = radd(d, b1, c234);

    let (_, target, quantity_eq) = telescope_le4(d, p, head, p1, p2, p3, tail);
    let at_quantity = rat_eq_rewrite(d, q1234, target, quantity_eq, s1234, &|d, t| {
        rle(d, rat, t, c1234)
    });

    let (final_bound, k_total, bound_eq) = fuse_bridge_bound(d, p, smm, n, k, zero_nat);
    let moved = rat_eq_rewrite(d, c1234, final_bound, bound_eq, at_quantity, &|d, t| {
        rle(d, rat, target, t)
    });

    let bound_final = div_succ_at(d, p, k_total, n);
    let nds2_smm = div_succ(d, p, 2, smm);

    let neg_bound_final = rneg(d, bound_final);
    let refl_neg_bf = d.lemma(rat.le_refl, &[neg_bound_final]);
    let subtracted = d.lemma(
        rat.add_le_add,
        &[
            target,
            final_bound,
            neg_bound_final,
            neg_bound_final,
            moved,
            refl_neg_bf,
        ],
    );
    let lhs_sub = radd(d, target, neg_bound_final);
    let (cancel_target, cancel_eq) = add_sub_cancel(d, p, nds2_smm, bound_final);
    let rhs_before = radd(d, final_bound, neg_bound_final);
    let after_cancel = rat_eq_rewrite(
        d,
        rhs_before,
        cancel_target,
        cancel_eq,
        subtracted,
        &|d, t| rle(d, rat, lhs_sub, t),
    );

    let doubled = doubled_half_shift_le(d, p, mm);
    let two_mm = div_succ(d, p, 2, mm);
    let final_at_mm = d.lemma(
        rat.le_trans,
        &[lhs_sub, nds2_smm, two_mm, after_cancel, doubled],
    );

    (k_total, final_at_mm)
}

/// From `hp : Within (rsub (sample x n) (sample y n)) (natDivSucc k n)`,
/// derive `(k_total, close_within x y (natDivSucc k_total n))` — lifting a
/// per-index rational sample bound to a genuine real inequality, via
/// [`shifted_bound_at`] in both directions (`CReal.abs_le`'s two premises)
/// and `Rat.neg_sub` bridging the sign for the negated one (mirroring
/// `declare_converges_upper_bound`'s own use of the same lemma for the same
/// reason).
fn close_within_of_sample_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    n: ExprId,
    k: ExprId,
    hp: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let nat = d.nat_ty();
    let qx = sample(d, p, x, n);
    let qy = sample(d, p, y, n);
    let diff = rsub(d, rat, qx, qy);
    let bound_k = div_succ_at(d, p, k, n);
    let (hp_lower, hp_upper) = halves(d, p, diff, bound_k, hp);

    let (k_total, le1) = {
        let mm_fv = d.fresh_fvar();
        let mm = d.kernel().fvar(mm_fv);
        let (kt, at_mm) = shifted_bound_at(d, p, x, y, n, k, hp_upper, mm);
        (kt, d.lam_fv(mm_fv, nat, at_mm))
    };
    let bound_final = div_succ_at(d, p, k_total, n);

    let le2 = {
        let neg_diff = rneg(d, diff);
        let mirror = rsub(d, rat, qy, qx);
        let w_neg = d.lemma(rat.bounds_neg, &[diff, bound_k, hp_lower, hp_upper]);
        let (_, r2_neg) = halves(d, p, neg_diff, bound_k, w_neg);
        let neg_sub_eq = d.lemma(rat.neg_sub, &[qx, qy]); // Eq neg_diff mirror
        let upper_yx = rat_eq_rewrite(d, neg_diff, mirror, neg_sub_eq, r2_neg, &|d, t| {
            rle(d, rat, t, bound_k)
        });

        let mm_fv = d.fresh_fvar();
        let mm = d.kernel().fvar(mm_fv);
        let (_, at_mm) = shifted_bound_at(d, p, y, x, n, k, upper_yx, mm);

        let smm = shift(d, mm);
        let head = sample(d, p, x, smm);
        let tail = sample(d, p, y, smm);
        let head_minus_tail = rsub(d, rat, head, tail);
        let a_term = rneg(d, head_minus_tail);
        let b_term = rsub(d, rat, tail, head);
        let ab_eq = d.lemma(rat.neg_sub, &[head, tail]); // Eq a_term b_term
        let ba_eq = rsymm(d, a_term, b_term, ab_eq); // Eq b_term a_term

        let two_mm = div_succ(d, p, 2, mm);
        let bridged = rat_eq_rewrite(d, b_term, a_term, ba_eq, at_mm, &|d, t| {
            let t_minus_bound = rsub(d, rat, t, bound_final);
            rle(d, rat, t_minus_bound, two_mm)
        });
        d.lam_fv(mm_fv, nat, bridged)
    };

    let v_term = {
        let neg_y = d.const_app(p.neg, &[y]);
        d.const_app(p.add, &[x, neg_y])
    };
    let embedded_bound = embed(d, p, bound_final);
    let close = d.lemma(p.abs_le, &[v_term, embedded_bound, le1, le2]);
    (k_total, close)
}

/// From `h_close : close_within x y q1` and `h_rat_le : Rat.le q1 q2`,
/// derive `close_within x y q2` — `CReal.ofRat_le` (the embedding is
/// monotone) plus `CReal.le_trans`.
fn weaken_close_within(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    q1: ExprId,
    q2: ExprId,
    h_close: ExprId,
    h_rat_le: ExprId,
) -> ExprId {
    let ny = d.const_app(p.neg, &[y]);
    let diff = d.const_app(p.add, &[x, ny]);
    let abs_diff = d.const_app(p.abs, &[diff]);
    let e1 = embed(d, p, q1);
    let e2 = embed(d, p, q2);
    let embed_le = d.lemma(p.of_rat_le, &[q1, q2, h_rat_le]);
    d.lemma(p.le_trans, &[abs_diff, e1, e2, h_close, embed_le])
}

/// `(target, Eq (mul (natDivSucc num 0) (natDivSucc 1 idx)) target)`, where
/// `target := natDivSucc num idx` — factoring an arbitrary-numerator bound
/// as a nonnegative constant times a numerator-`1` one (`Rat.natDivSucc_mul`
/// plus `Nat.mul_one`), the piece [`nat_div_succ_antitone_general`] needs
/// twice.
fn factor_nat_div_succ(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    num: ExprId,
    idx: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let cc = div_succ_at(d, p, num, zero_nat);
    let nd1_idx = div_succ(d, p, 1, idx);
    let cmul_term = rmul(d, cc, nd1_idx);
    let fuse = d.lemma(rat.nat_div_succ_mul, &[num, one_nat, idx]); // Eq cmul_term (natDivSucc (num*1) idx)
    let num_mul_one = NatOps::mul(d, num, one_nat);
    let almost = div_succ_at(d, p, num_mul_one, idx);
    let trim = d.lemma(rat.int.nat.mul_one, &[num]); // Eq (num*1) num
    let target = div_succ_at(d, p, num, idx);
    let tidy = nat_eq_to_rat(d, num_mul_one, num, trim, &|d, t| div_succ_at(d, p, t, idx));
    let (_, combined) = rchain(d, cmul_term, &[(almost, fuse), (target, tidy)]);
    (target, combined)
}

/// From `h_lo_hi : Nat.le lo hi`, derive `Rat.le (natDivSucc num hi)
/// (natDivSucc num lo)` — antitonicity in the index for an ARBITRARY
/// numerator `num`, built by factoring `natDivSucc num X` as `(natDivSucc
/// num 0) * (natDivSucc 1 X)` at both `X := hi` and `X := lo`
/// ([`factor_nat_div_succ`]), then transporting `Rat.natDivSucc_antitone`'s
/// numerator-`1` comparison through the nonnegative constant `natDivSucc
/// num 0` (`Rat.mul_le_mul_of_nonneg_left`). `Rat.natDivSucc_antitone`
/// itself only ever compares numerator `1`; this is the module's own
/// mechanism to keep it off the critical path a second time
/// (`Rat.natDivSucc_scale`'s doc), generalised to `converges_comp_eventually`'s
/// numerator, which is not fixed at `1`.
fn nat_div_succ_antitone_general(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    num: ExprId,
    lo: ExprId,
    hi: ExprId,
    h_lo_hi: ExprId,
) -> ExprId {
    let rat = p.rat;
    let (nd_num_hi, factor_hi_eq) = factor_nat_div_succ(d, p, num, hi);
    let (nd_num_lo, factor_lo_eq) = factor_nat_div_succ(d, p, num, lo);
    let zero_nat = d.num(0);
    let cc = div_succ_at(d, p, num, zero_nat);
    let nd1_hi = div_succ(d, p, 1, hi);
    let nd1_lo = div_succ(d, p, 1, lo);
    let cmul_hi = rmul(d, cc, nd1_hi);
    let cmul_lo = rmul(d, cc, nd1_lo);

    let antitone = d.lemma(rat.nat_div_succ_antitone, &[lo, hi, h_lo_hi]); // Rat.le nd1_hi nd1_lo
    let nonneg_cc = d.lemma(rat.zero_le_nat_div_succ, &[num, zero_nat]);
    let scaled = d.lemma(
        rat.mul_le_mul_of_nonneg_left,
        &[cc, nd1_hi, nd1_lo, nonneg_cc, antitone],
    );

    let at_hi = rat_eq_rewrite(d, cmul_hi, nd_num_hi, factor_hi_eq, scaled, &|d, t| {
        rle(d, rat, t, cmul_lo)
    });
    rat_eq_rewrite(d, cmul_lo, nd_num_lo, factor_lo_eq, at_hi, &|d, t| {
        rle(d, rat, nd_num_hi, t)
    })
}

/// `CReal.converges_comp_eventually : ∀ F a b (u : UniformlyContinuousOn F a
/// b) f L, (∀ n, le a (f n)) → (∀ n, le (f n) b) → Converges f L → ∀ e, ∃ N,
/// ∀ n, Nat.le N n → close_within (F (f n)) (F L) (natDivSucc 1 e)`.
///
/// See `CRealPrelude::converges_comp_eventually`'s own doc and this file's
/// module documentation just above for why this eventual form, not the
/// fixed-rate one, is the true statement. `le a L`/`le L b` are derived
/// (`converges_lower_bound`/`converges_upper_bound`), not assumed.
///
/// `N := succ M0`, `M0 := (K'+1)·(modulus e) + K'` where `K' := succ
/// k_total` and `k_total` is [`fuse_bridge_bound`]'s own padded numerator
/// (the `+4`-ish slack `close_within_of_sample_bound`'s real-valued lift
/// costs on top of the raw `Converges` witness `K`) — `Rat.natDivSucc_scale`
/// at `(c, m) := (k_total, modulus e)` reads exactly this index back to
/// `natDivSucc 1 (modulus e)`, no `Nat` division or search, `modulus` only
/// ever evaluated forward at `e`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// refused a proof, not that a script gave up.
pub(super) fn declare_converges_comp_eventually(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = fn_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);

    let f_big_fv = d.fresh_fvar();
    let f_big = d.kernel().fvar(f_big_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f_big, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);

    let lower_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let claim = d.const_app(p.le, &[a, fn_term]);
        d.pi_fv(n_fv, nat, claim)
    };
    let h_lo_fv = d.fresh_fvar();
    let h_lo = d.kernel().fvar(h_lo_fv);

    let upper_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let claim = d.const_app(p.le, &[fn_term, b]);
        d.pi_fv(n_fv, nat, claim)
    };
    let h_hi_fv = d.fresh_fvar();
    let h_hi = d.kernel().fvar(h_hi_fv);

    let converges_fl = converges_applied(d, p, f, l);
    let hconv_fv = d.fresh_fvar();
    let hconv = d.kernel().fvar(hconv_fv);

    // `∀ e, ∃ N, ∀ n, Nat.le N n → close_within (F (f n)) (F L) (natDivSucc
    // 1 e)` -- the target of `exists_elim` below; it does not mention
    // `Converges`'s witness `K`.
    let target_ty = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let body = comp_conclusion_ty(d, p, f_big, f, l, e);
        d.pi_fv(e_fv, nat, body)
    };

    let ha_l = d.lemma(p.converges_lower_bound, &[a, f, l, h_lo, hconv]);
    let hl_b = d.lemma(p.converges_upper_bound, &[f, l, b, h_hi, hconv]);

    let predicate = converges_predicate(d, p, f, l);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = converges_body(d, p, f, l, k);
        let hp_fv = d.fresh_fvar();
        let hp_all = d.kernel().fvar(hp_fv);

        let zero_nat = d.num(0);
        let k_total = bridge_total_numerator(d, k, zero_nat);
        let k_total_prime = d.succ(k_total);

        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let body_over_e = {
            let modulus_fn = d.const_app(p.uc_modulus, &[f_big, a, b, u]);
            let m_e = d.apply(modulus_fn, &[e]);

            let m0 = {
                let product = NatOps::mul(d, k_total_prime, m_e);
                NatOps::add(d, product, k_total)
            };
            let big_n = d.succ(m0);
            let scale_eq = d.lemma(rat.nat_div_succ_scale, &[k_total, m_e]);

            let pred = comp_predicate(d, p, f_big, f, l, e);
            let per_n_body = {
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let hn_fv = d.fresh_fvar();
                let hn = d.kernel().fvar(hn_fv);
                let hn_ty = d.le(big_n, n);

                let le_succ_m0 = d.lemma(rat.int.nat.le_succ, &[m0]);
                let h_m0_n = d.lemma(rat.int.nat.le_trans, &[m0, big_n, n, le_succ_m0, hn]);

                let hp_n = d.apply(hp_all, &[n]);
                let fn_n = d.apply(f, &[n]);
                let (_, close_kn) = close_within_of_sample_bound(d, p, fn_n, l, n, k, hp_n);
                let bound_final = div_succ_at(d, p, k_total, n);

                let one_nat = d.num(1);
                let widen = d.lemma(rat.nat_div_succ_le_add_left, &[k_total, one_nat, n]);
                let antitone_kp = nat_div_succ_antitone_general(d, p, k_total_prime, m0, n, h_m0_n);
                let mid = div_succ_at(d, p, k_total_prime, n);
                let far = div_succ_at(d, p, k_total_prime, m0);
                let step12 = d.lemma(rat.le_trans, &[bound_final, mid, far, widen, antitone_kp]);
                let one_over_me = div_succ(d, p, 1, m_e);
                let scaling_proof =
                    rat_eq_rewrite(d, far, one_over_me, scale_eq, step12, &|d, t| {
                        rle(d, rat, bound_final, t)
                    });

                let weakened = weaken_close_within(
                    d,
                    p,
                    fn_n,
                    l,
                    bound_final,
                    one_over_me,
                    close_kn,
                    scaling_proof,
                );

                let h_a_fn = d.apply(h_lo, &[n]);
                let h_fn_b = d.apply(h_hi, &[n]);
                let spec_term = d.const_app(p.uc_spec, &[f_big, a, b, u]);
                let applied = d.apply(
                    spec_term,
                    &[e, fn_n, l, h_a_fn, h_fn_b, ha_l, hl_b, weakened],
                );

                let with_hn = d.lam_fv(hn_fv, hn_ty, applied);
                d.lam_fv(n_fv, nat, with_hn)
            };
            exists_intro(d, p, nat, pred, big_n, per_n_body)
        };
        let per_e = d.lam_fv(e_fv, nat, body_over_e);

        let with_hp = d.lam_fv(hp_fv, hp_ty, per_e);
        d.lam_fv(k_fv, nat, with_hp)
    };

    let proof_body = exists_elim(d, p, nat, predicate, target_ty, hconv, minor);

    let value = {
        let with_hconv = d.lam_fv(hconv_fv, converges_fl, proof_body);
        let with_h_hi = d.lam_fv(h_hi_fv, upper_ty, with_hconv);
        let with_h_lo = d.lam_fv(h_lo_fv, lower_ty, with_h_hi);
        let with_l = d.lam_fv(l_fv, carrier, with_h_lo);
        let with_f = d.lam_fv(f_fv, seq_ty, with_l);
        let with_u = d.lam_fv(u_fv, u_ty, with_f);
        let with_b = d.lam_fv(b_fv, carrier, with_u);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(f_big_fv, func_ty, with_a)
    };
    let ty = {
        let after_hconv = d.arrow(converges_fl, target_ty);
        let after_h_hi = d.arrow(upper_ty, after_hconv);
        let after_h_lo = d.arrow(lower_ty, after_h_hi);
        let with_l = d.pi_fv(l_fv, carrier, after_h_lo);
        let with_f = d.pi_fv(f_fv, seq_ty, with_l);
        let with_u = d.pi_fv(u_fv, u_ty, with_f);
        let with_b = d.pi_fv(b_fv, carrier, with_u);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(f_big_fv, func_ty, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_comp_eventually,
        uparams: vec![],
        ty,
        value,
    })
}
