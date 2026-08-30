//! The quotient-form geometric tail bound, `CReal.geom_tail_bounded_div`.
//!
//! ## Why `PosBound (1 − x) k` is data, not a hypothesis on `x`
//!
//! [`power.rs`](super::power)'s own module documentation is explicit that
//! [`CRealPrelude::geom_tail_bounded`] stops at the multiplied-through form
//! `(1 − x) · tail ≤ xᵐ`, precisely because turning it into a bound on `tail`
//! alone needs `inv (1 − x)`, and `CReal.inv` needs a **witnessed**
//! [`CRealPrelude::pos_bound`] — a rational modulus `k` together with a proof
//! that every sample of `1 − x` from index `k` onward is at least `1/(k+1)`.
//! `0 ≤ x` says nothing about how close `x` is to `1`; `x` could be `Equiv`
//! to `one` itself, in which case `1 − x` is not apart from zero and no such
//! `k` exists. Deriving one from `x < 1` (`CReal.lt`, an `Exists`) would work
//! for a caller who already has it, but there is no way to *manufacture* one
//! from `0 ≤ x` alone — over `CReal`, `le` is undecidable, `Apart` is an `Or`
//! whose `Or.rec` does not eliminate into `Type`, and this kernel has no
//! Markov principle. So "`x` bounded away from `1`" is carried as the same
//! kind of data [`CRealPrelude::inv`] and
//! [`CRealPrelude::le_of_mul_le_mul_left`] already carry: a `PosBound (add
//! one (neg x)) k` witness, taken as a hypothesis rather than derived. A
//! caller who already knows `x < 1` gets one for free via
//! [`CRealPrelude::pos_bound_of_lt`] (mirroring `cancellation.rs`'s own
//! remark that this asks for nothing a `0 < c` caller does not already have).
//!
//! This is a genuinely per-construction decision, not a house convention:
//! `CReal.sqrt` needs no such witness because its clamp and fixed schedule
//! make it total over every input, with no apartness-from-zero anywhere in
//! its construction.
//!
//! ## The derivation
//!
//! [`declare_geom_tail_bounded_div`] takes `h_dom : le (mul a tail) (pow x
//! m)` ([`CRealPrelude::geom_tail_bounded`], `a := add one (neg x)`) and
//! multiplies through by `inv a k h` (nonnegative,
//! [`CRealPrelude::inv_nonneg`]) via
//! [`CRealPrelude::mul_le_mul_of_nonneg_left`], giving `le (mul inv (mul a
//! tail)) (mul inv (pow x m))`. The left side collapses to `tail` by the same
//! `mul inv (mul c w) ≈ w` identity `cancellation.rs::declare_
//! le_of_mul_le_mul_left` uses internally (reproduced here as [`cancel_left`]
//! rather than imported — it is a private `fn` there, per this slice's
//! constraint of not editing that file, and the precedent for reproducing a
//! sibling module's private helper verbatim is `cancellation.rs` itself,
//! which reproduces several of `inverse.rs`'s). [`CRealPrelude::le_congr`]
//! transports the inequality across that one `Equiv`, landing directly on
//! `le tail (mul inv (pow x m))` — the quotient form, `tail ≤ xᵐ / (1 − x)`.
//!
//! This does **not** go through
//! [`CRealPrelude::le_of_mul_le_mul_left`]'s own `le (mul c x) (mul c y) →
//! le x y` wrapper: that shape needs `geom_tail_bounded`'s right-hand side
//! `pow x m` already rewritten as `mul a (mul inv (pow x m))` before the
//! wrapper applies, which itself needs the same cancellation identity run in
//! the opposite orientation (`mul_inv_cancel` commuted) — strictly more work
//! than applying `mul_le_mul_of_nonneg_left` once and cancelling the side
//! that is already in the right shape.
//!
//! ## `CReal.geom_tail_within`, and exactly what it does and does not close
//!
//! The goal this file was extended for is `Cauchy (sumRange (fun n => pow x
//! n))`. `series.rs`'s own six-stage pipeline
//! (`sum_range_tail_within` → `_within_le` → `_tail_cauchy_within` →
//! `_within_cauchy` → `_cauchy_dominated_ordered` → `_ordered_normalized`)
//! is hardwired around **two** sequences `f`/`g` with a pointwise-domination
//! hypothesis plus an already-witnessed raw `Cauchy` proof for `g` — taking
//! `f = g = pow x ·` is circular, since nothing here has a `g` other than the
//! sequence being proved Cauchy in the first place.
//!
//! [`declare_geom_tail_within`] is the self-contained analogue of the
//! pipeline's first stage, [`CRealPrelude::sum_range_tail_within`]: it
//! repackages a real-valued tail bound as a rational `Within` bound at the
//! tail's own canonical index `add m n`, deferring the "other side" (there,
//! `g`'s own tail sample; here, `Yₘ := xᵐ/(1−x)`'s own sample) rather than
//! closing it into a fixed constant. It needs no `g` and no external Cauchy
//! witness — only [`CRealPrelude::geom_tail_bounded_div`] (`tail ≤ Yₘ`) and a
//! fresh nonnegativity proof for the tail (`geom_tail_nonneg`, built below
//! from [`CRealPrelude::sum_range_split`] + [`CRealPrelude::pow_nonneg`],
//! since `series.rs`'s own module documentation lists a nonnegativity lemma
//! for `sumRange` of a pointwise-nonnegative function among what it does
//! **not** build) to get `0 ≤ tail ≤ Yₘ`, hence `−Yₘ ≤ tail ≤ Yₘ`, then
//! applies both real inequalities directly to the index `add m n` (`CReal.le`
//! is a `Definition` — `le x y := ∀ n, seq x n − seq y n ≤ 2/(n+1)` — so a
//! proof of it can be `.apply()`'d to a `Nat` argument exactly the way
//! `series.rs`'s own `declare_sum_range_tail_within` applies `r1`/`r2` to
//! `add m n`) and closes with the same "within-swap via `neg_sub`" helper
//! (`within_of_tail_le`, reproduced verbatim below — private to `series.rs`).
//!
//! **This is not yet `Cauchy`, and landing it alone would not finish the
//! goal — but the goal itself is now closed, in `exponential.rs`, and the
//! diagnosis below turned out to name a blocker that had already been
//! removed by unrelated work.** Reaching `Cauchy`'s own `∃ K, ∀ m n, Within
//! (…) (natDivSucc K m + natDivSucc K n)` shape from `geom_tail_within`
//! needs bounding the deferred sample `seq Yₘ (add m n)` — a quantity that
//! decays **geometrically** in `m` — by a **harmonic**-shaped `natDivSucc
//! K' m` for one `K'` fixed *uniformly in `m`*. This paragraph used to say
//! "there is no lemma bounding `CReal.pow` above by a `natDivSucc`
//! rational", and that was true when it was written — but
//! `CRealPrelude::pow_half_le_nat_div_succ`, added to *this file* later (for
//! the IVT bisection modulus, `ivt.rs`), is exactly that lemma at the
//! concrete base `1/2`. Nothing else in the "no comparing `pow` at two
//! different bases" / "no Bernoulli-type inequality" pair was ever built or
//! needed: the base-`1/2` route only ever needed the one harmonic bound,
//! not a general comparison. `exponential.rs`'s own module documentation
//! has the corrected account and the full derivation
//! (`CReal.geomHalfInvLeafBound` → `CReal.geomCauchyOrderedHalf` →
//! `CReal.geomCauchy`, the last of these `Cauchy (sumRange (fun n => pow
//! half n))` itself).
//!
//! ## `geom_tail_within_le` and `geom_pair_within`: the index generalization
//! and the canonical-index normalization, landed without the harmonic bound
//!
//! [`declare_geom_tail_within_le`] is stage 2 of `series.rs`'s pipeline
//! (`_within_le`), reproduced against `geom_tail_within` instead of
//! `sum_range_tail_within`: `Nat.le_dest` plus `nat_rewrite_prop` lift the
//! ordered-pair shape `(m, add m n)` to an arbitrary pair `(a, b)`
//! constrained only by `a ≤ b`. Purely index bookkeeping, no new real-analysis
//! content.
//!
//! [`declare_geom_pair_within`] is the genuinely new piece: the
//! canonical-index normalization `series.rs` calls stages 5+6
//! (`_cauchy_dominated_ordered` + `_ordered_normalized`), landed for this
//! single sequence *without* going through a separately-witnessed `Cauchy`
//! hypothesis for a comparison sequence `g` — because there is no such `g`
//! here. It chains four points `Y → X → W → Z` via [`chain_within3`]
//! (reproduced from `series.rs::dominated_canonical_at`, private there):
//! `Y := seq (sumRange f b) b`, `X := seq (sumRange f b) (shift b)`,
//! `W := seq (sumRange f a) (shift b)`, `Z := seq (sumRange f a) a`. The two
//! outer legs (`Y−X`, `W−Z`) are [`CRealPrelude::regular`] applied to
//! `sumRange f b` / `sumRange f a` themselves — a fact true of *any* `CReal`,
//! needing no domination — and the middle leg (`X−W`) is defeq to
//! [`declare_geom_tail_within_le`]'s own conclusion at `(a, b)`, by the same
//! ι/β argument `geom_tail_within`'s own doc comment already gives for why no
//! separate `Eq` lemma is needed to see `seq (add p (neg q)) k` as `seq p
//! (shift k) − seq q (shift k)`. The result:
//!
//! ```text
//! CReal.geom_pair_within : ∀ x, 0 ≤ x → ∀ k (h : PosBound (1−x) k) a b,
//!   a ≤ b → Within (seq (sumRange f b) b − seq (sumRange f a) a)
//!                  ((modulus (shift b) b + (seq Yₐ b + natDivSucc 2 b))
//!                   + modulus a (shift b))
//! ```
//!
//! **This closes the "ordering split and normalization" gap the geometric
//! lane's own diagnosis named, for the ordered pair `a ≤ b`.** What it does
//! *not* do, and why stopping here is deliberate rather than an oversight:
//!
//! 1. **The `seq Yₐ b` leaf is still the undischarged sample this module's
//!    previous section names** — the harmonic-shaped bound on `Yₘ` uniform in
//!    `m` remains missing, for the same reason (`pow`-vs-`natDivSucc`
//!    comparison, base comparison, or Bernoulli — none exist yet). This
//!    theorem does not need any of them; it only needed `geom_tail_within_le`
//!    and `CReal.regular`, so landing it does not depend on the missing
//!    piece, but consuming it toward `Cauchy` still does.
//! 2. **The `Nat.le_total` case split removing the `a ≤ b` hypothesis is left
//!    unbuilt, deliberately, matching `series.rs`'s own
//!    `sum_range_cauchy_dominated_ordered_normalized`, whose doc comment
//!    explicitly defers exactly this split to "whichever piece assembles
//!    `sum_range_cauchy_of_dominated` next."** Removing it here would need a
//!    single closed-form bound symmetric in `a`/`b`, and this development has
//!    no `Nat.max` (`nat_prelude` deliberately uses `add`-based bounds
//!    instead, per `creal.rs`'s own `has_derivative_add` doc comment) and no
//!    generic `Within r q → 0 ≤ q` fact to let a `0 ≤ total(other order)`
//!    weakening substitute for one. Either is buildable, but neither exists
//!    yet, and a future consumer that already knows which of `m ≤ n` or
//!    `n ≤ m` holds (e.g. by running the same `Nat.le_total` split itself) can
//!    call `geom_pair_within` directly at whichever orientation applies,
//!    exactly the way `dominated_canonical_at`'s own two callers do.
//! 3. Leaf-fusion/widening (collapsing the five-leaf bound above into a
//!    single `natDivSucc` per side the way
//!    `sum_range_cauchy_dominated_ordered_normalized` does for the dominated
//!    case) is cosmetic bookkeeping, not attempted here: it would not change
//!    what is blocked (the `seq Yₐ b` leaf still would not fuse into a
//!    `natDivSucc` shape without the harmonic bound), so it was not worth the
//!    machinery for this slice.
//!
//! ## The RAW (non-existential) family, and why it is not more arithmetic
//!
//! Everything above proves `Prop`s. A `Type`-valued consumer cannot use them:
//! [`CRealPrelude::mk`]'s regularity argument and
//! [`CRealPrelude::weierstrass_m_test`]'s `hcauchy` parameter both need a
//! **raw** `(k, proof)` pair, and `Exists.rec` is `Prop`-only, so an `∃ K, …`
//! can never be unwrapped into either. `creal/trig_fn.rs`'s module
//! documentation traces all three rungs of a Spivak-ch.15 π to exactly this,
//! and sizes the fix at "~150-300 new lines, redoing this file's chain
//! EXPLICITLY for one chosen literal ratio".
//!
//! **It is neither new arithmetic nor ratio-specific, and it needed no new
//! proof content at all.** [`declare_geom_cauchy_of_lt_ordered`] already takes
//! its leaf-bound witness `(bigK, hK)` as explicit parameters at a fully
//! general ratio -- it was raw the whole time. The only two `Exists` in the
//! chain above it are introduced at the very END of two proofs whose bodies
//! are already non-existential:
//!
//! * [`declare_pow_le_nat_div_succ_of_lt`] eliminates `lt x one` for a
//!   rational gap `q` and [`CRealPrelude::pos_bound_of_lt`] for a modulus
//!   `k3`, then hides the witness `Nat.succ k3` behind an `Exists.intro`.
//! * [`declare_geom_y_bound`] eliminates that one, then hides
//!   `(Nat.succ k)*k1` behind another.
//!
//! So each body is factored into a shared Rust helper and declared twice --
//! once existentially (unchanged statement, unchanged proof term) and once
//! raw:
//!
//! | raw | existential twin | shared body |
//! |---|---|---|
//! | `CReal.pow_le_natDivSucc_of_gap` | `CReal.pow_le_natDivSucc_of_lt` | [`pow_le_nat_div_succ_gap_leaf`] |
//! | `CReal.geomYBoundRaw` | `CReal.geomYBound` | [`geom_y_bound_leaf`] |
//! | `CReal.geomCauchyOrderedOfGap` | -- | pure composition |
//! | `CReal.geomCauchyBodyOfGap` | `CReal.geomCauchy` (base 1/2 only) | the same `Nat.le_total` split, minus the `Exists.intro` |
//!
//! Both raw forms DROP the `lt x one` hypothesis, which existed only to
//! manufacture the witnesses, and `pow_le_natDivSucc_of_gap` additionally
//! drops `Rat.lt Rat.zero q` (its `le zero (ofRat q)` comes from `h_pb`).
//! What a caller owes at a chosen ratio is therefore only rational: a gap `q`
//! with `x + q ≤ 1`, and two `PosBound` moduli.
//!
//! [`declare_geom_cauchy_ordered_16_over_25`] /
//! [`declare_geom_cauchy_body_16_over_25`] are the first instantiation, at
//! `16/25`. Read that first function's doc comment before choosing a
//! different ratio -- in particular, the `9/16` that circulates in the notes
//! comes from `R := 3/2 = 1.5`, which is BELOW cosine's first zero (≈1.5708)
//! and so would not have unblocked π. Adding `49/64` (`R := 7/4`) is a copy of
//! [`ratio_16_over_25_witnesses`] with three numerals changed.

use super::series::{
    assoc_rev_eq, exists_nat_intro, fuse_same_index, neg_zero_equiv, sum_range_cauchy_body,
};
use super::{
    CRealPrelude, and_intro, creal_ty, div_succ, embed, equiv, gap_elim, gap_halves, halves,
    modulus, sample, shift, weaken, within,
};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::RatPrelude;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{
    nat_eq_to_rat, nat_rewrite_prop, radd, rat_eq_rewrite, rat_ty, rchain, rcongr, req, rle, rlt,
    rmul, rneg, rone, rpow, rsymm, rtrans, rzero,
};

// --- small local term builders, verbatim in shape to every other `creal/*`
// module's own copies (see e.g. `power.rs`, `cancellation.rs`) -------------

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn cle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.le, &[x, y])
}

fn cinv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId, h: ExprId) -> ExprId {
    d.const_app(p.inv, &[x, k, h])
}

fn pos_bound_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.pos_bound, &[x, k])
}

/// `λ i, CReal.pow x i` — verbatim copy of `power.rs::pow_fn`, reproduced so
/// this file's own `sumRange` applications are built from the identical
/// closure shape `geom_tail_bounded`'s own statement uses (both built the
/// same way, from a fresh bound variable via `lam_fv`, so the kernel accepts
/// them as the same term up to alpha-equivalence when this file applies
/// `p.geom_tail_bounded`).
fn pow_fn(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = d.const_app(p.pow, &[x, i]);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// `Equiv (mul inv_expr (mul c w)) w`, given `cancel_proof : Equiv (mul c
/// inv_expr) one`. Verbatim copy of `cancellation.rs::cancel_left` (private
/// there): `mul inv_expr (mul c w) ≈ mul (mul inv_expr c) w` (`mul_assoc`,
/// reversed) `≈ mul (mul c inv_expr) w` (`mul_comm`) `≈ mul one w`
/// (`cancel_proof`) `≈ mul w one` (`mul_comm`) `≈ w` (`mul_one`).
fn cancel_left(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    inv_expr: ExprId,
    c: ExprId,
    w: ExprId,
    cancel_proof: ExprId,
) -> ExprId {
    let cw = cmul(d, p, c, w);
    let start = cmul(d, p, inv_expr, cw);

    let inv_c = cmul(d, p, inv_expr, c);
    let step_a_target = cmul(d, p, inv_c, w);
    let assoc = d.lemma(p.mul_assoc, &[inv_expr, c, w]);
    let step_a = d.lemma(p.equiv_symm, &[step_a_target, start, assoc]);

    let c_inv = cmul(d, p, c, inv_expr);
    let comm_ic = d.lemma(p.mul_comm, &[inv_expr, c]);
    let refl_w = d.lemma(p.equiv_refl, &[w]);
    let step_b_target = cmul(d, p, c_inv, w);
    let step_b = d.lemma(p.mul_congr, &[inv_c, c_inv, w, w, comm_ic, refl_w]);

    let one = d.kernel().const_(p.one, vec![]);
    let step_c_target = cmul(d, p, one, w);
    let step_c = d.lemma(p.mul_congr, &[c_inv, one, w, w, cancel_proof, refl_w]);

    let step_d_target = cmul(d, p, w, one);
    let step_d = d.lemma(p.mul_comm, &[one, w]);

    let step_e = d.lemma(p.mul_one, &[w]);

    echain(
        d,
        p,
        start,
        &[
            (step_a_target, step_a),
            (step_b_target, step_b),
            (step_c_target, step_c),
            (step_d_target, step_d),
            (w, step_e),
        ],
    )
}

/// `Equiv`-chain composition. Verbatim copy of `cancellation.rs::echain`
/// (private there, and identical in shape to every other `creal/*` module's
/// own private copy — see e.g. `power.rs::echain`, `series.rs::echain`).
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

/// `CReal.geom_tail_bounded_div : ∀ x, le zero x → ∀ k (h : PosBound (add one
/// (neg x)) k) m n, le (add (sumRange (fun j => pow x j) (Nat.add m n)) (neg
/// (sumRange (fun j => pow x j) m))) (mul (inv (add one (neg x)) k h) (pow x
/// m))`. See the module documentation for the derivation and for why `h` is
/// data rather than a hypothesis on `x`.
fn declare_geom_tail_bounded_div(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let nat_add = d.prelude().add;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_x = cneg(d, p, x);
    let a = cadd(d, p, one, neg_x); // a = 1 - x
    let hyp_pos_bound = pos_bound_of(d, p, a, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mn = d.const_app(nat_add, &[m, n]);
    let f = pow_fn(d, p, x);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let sum_f_mn = d.const_app(p.sum_range, &[f, mn]);
    let neg_sum_f_m = cneg(d, p, sum_f_m);
    let tail = cadd(d, p, sum_f_mn, neg_sum_f_m);

    let pow_m = d.const_app(p.pow, &[x, m]);

    let hyp0 = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, x)
    };

    // h_dom : le (mul a tail) pow_m
    let h_dom = d.lemma(p.geom_tail_bounded, &[x, h0, m, n]);

    let inv_expr = cinv(d, p, a, k, h);
    let inv_nonneg_fact = d.lemma(p.inv_nonneg, &[a, k, h]);

    let lhs_mul = cmul(d, p, a, tail);
    // step1 : le (mul inv_expr lhs_mul) (mul inv_expr pow_m)
    let step1 = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[inv_expr, lhs_mul, pow_m, inv_nonneg_fact, h_dom],
    );

    // cancel_proof : Equiv (mul a inv_expr) one
    let cancel_proof = d.lemma(p.mul_inv_cancel, &[a, k, h]);
    // eq_tail : Equiv (mul inv_expr (mul a tail)) tail
    let eq_tail = cancel_left(d, p, inv_expr, a, tail, cancel_proof);

    let mul_inv_lhs = cmul(d, p, inv_expr, lhs_mul);
    let mul_inv_pow_m = cmul(d, p, inv_expr, pow_m);
    let refl_rhs = d.lemma(p.equiv_refl, &[mul_inv_pow_m]);
    // proof_inner : le tail mul_inv_pow_m
    let proof_inner = d.lemma(
        p.le_congr,
        &[
            mul_inv_lhs,
            tail,
            mul_inv_pow_m,
            mul_inv_pow_m,
            eq_tail,
            refl_rhs,
            step1,
        ],
    );

    let stmt_inner = cle(d, p, tail, mul_inv_pow_m);

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_m = d.pi_fv(m_fv, nat, inner);
        // `h_fv` escapes into `with_m` through `mul_inv_pow_m` (via
        // `inv_expr`), so this Pi must be genuinely dependent (`pi_fv`), not
        // `d.arrow` -- the same trap `inv_nonneg`'s own `ty` names.
        let with_h = d.pi_fv(h_fv, hyp_pos_bound, with_m);
        let with_k = d.pi_fv(k_fv, nat, with_h);
        let with_h0 = d.arrow(hyp0, with_k);
        d.pi_fv(x_fv, carrier, with_h0)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_m = d.lam_fv(m_fv, nat, inner);
        let with_h = d.lam_fv(h_fv, hyp_pos_bound, with_m);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_h0 = d.lam_fv(h0_fv, hyp0, with_k);
        d.lam_fv(x_fv, carrier, with_h0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_tail_bounded_div,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `geom_tail_within` -----------------------------------------------------

/// `λ k, f (add m k)` — `f` shifted by `m`. Verbatim copy of
/// `series.rs::shifted_fn` (private there): the same construction, so that
/// [`CRealPrelude::sum_range_split`]'s own instantiated conclusion (which
/// embeds exactly this shape, substituted with our `f`/`m`) matches whatever
/// this file independently builds — `series.rs`'s own doc comment on
/// `shifted_fn` names this as the reason the two never build structurally
/// distinct (merely defeq) closures for the same summand.
fn shifted_fn(d: &mut IntDev<'_>, m: ExprId, f: ExprId) -> ExprId {
    let nat_add = d.prelude().add;
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let mk = d.const_app(nat_add, &[m, k]);
    let body = d.apply(f, &[mk]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Equiv (add (add a b) (neg a)) b` — the group cancellation `(a+b)+(−a) ~
/// b`. Verbatim copy of `series.rs::cancel_right` (private there).
fn cancel_right(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let ab = cadd(d, p, a, b);
    let start = cadd(d, p, ab, na);

    let ba = cadd(d, p, b, a);
    let comm1 = d.lemma(p.add_comm, &[a, b]); // ab ~ ba
    let refl_na = d.lemma(p.equiv_refl, &[na]);
    let s1 = cadd(d, p, ba, na);
    let h1 = d.lemma(p.add_congr, &[ab, ba, na, na, comm1, refl_na]);

    let a_na = cadd(d, p, a, na);
    let s2 = cadd(d, p, b, a_na);
    let h2 = d.lemma(p.add_assoc, &[b, a, na]); // s1 ~ s2

    let zero_c = czero(d, p);
    let h_an = d.lemma(p.add_neg, &[a]); // a_na ~ zero
    let refl_b = d.lemma(p.equiv_refl, &[b]);
    let s3 = cadd(d, p, b, zero_c);
    let h3 = d.lemma(p.add_congr, &[b, b, a_na, zero_c, refl_b, h_an]); // s2 ~ s3

    let h4 = d.lemma(p.add_zero, &[b]); // s3 ~ b

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (b, h4)])
}

/// From `Rat.le (Rat.sub u v) w` and `Rat.le (Rat.sub (Rat.neg u) v) w`,
/// derive `CReal.Within u (Rat.add v w)`. Verbatim copy of
/// `series.rs::within_of_tail_le` (private there).
fn within_of_tail_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    w: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let rat = p.rat;
    let vw = radd(d, v, w);

    let upper = d.lemma(rat.le_of_sub_le, &[u, v, w, h1]);

    let neg_u = rneg(d, u);
    let lower_neg = d.lemma(rat.le_of_sub_le, &[neg_u, v, w, h2]);

    let neg_vw = rneg(d, vw);
    let neg_neg_u = rneg(d, neg_u);
    let flipped = d.lemma(rat.neg_le_neg, &[neg_u, vw, lower_neg]);

    let nn = d.lemma(rat.neg_neg, &[u]);
    let lower = rat_eq_rewrite(d, neg_neg_u, u, nn, flipped, &|d, t| rle(d, rat, neg_vw, t));

    let lower_ty = rle(d, rat, neg_vw, u);
    let upper_ty = rle(d, rat, u, vw);
    and_intro(d, p, lower_ty, upper_ty, lower, upper)
}

/// `∀ i, le zero (pow x (add m i)) → …` folded into a proof of `le zero
/// (sumRange (shifted_fn m (pow_fn x)) n)` by induction on `n`. The
/// nonnegativity lemma `series.rs`'s own module documentation names as
/// **not** built anywhere in this development (needed for
/// [`CRealPrelude::geom_tail_bounded`]'s own real tail bound, and needed
/// again here): base case is `sumRange _ 0 ≡ zero` (`Nat.rec`'s own
/// ι-reduction, no named `sum_range_zero` lemma needed, mirroring
/// `power.rs::declare_pow_nonneg`'s own base case), the step combines the
/// inductive hypothesis with [`CRealPrelude::pow_nonneg`] at `add m j` via
/// [`CRealPrelude::add_le_add`] and folds `add zero zero` back to `zero`
/// with [`CRealPrelude::add_zero`] + [`CRealPrelude::le_congr`].
fn geom_shifted_sum_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    h0: ExprId,
    m: ExprId,
    n: ExprId,
) -> ExprId {
    let f = pow_fn(d, p, x);
    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let g = shifted_fn(d, m, f);
        let sg = d.const_app(p.sum_range, &[g, v]);
        let zero_c = czero(d, p);
        cle(d, p, zero_c, sg)
    };
    d.induct(
        &motive,
        &|d| {
            let zero_c = czero(d, p);
            d.lemma(p.le_refl, &[zero_c])
        },
        &|d, j, ih| {
            let nat_add = d.prelude().add;
            let m_plus_j = d.const_app(nat_add, &[m, j]);
            let hj_nonneg = d.lemma(p.pow_nonneg, &[x, h0, m_plus_j]);

            let g = shifted_fn(d, m, f);
            let sg_j = d.const_app(p.sum_range, &[g, j]);
            let gj = d.apply(g, &[j]);
            let zero_c = czero(d, p);
            let combined = d.lemma(p.add_le_add, &[zero_c, sg_j, zero_c, gj, ih, hj_nonneg]);
            // combined : le (add zero zero) (add sg_j gj)

            let add_zero_proof = d.lemma(p.add_zero, &[zero_c]); // Equiv (add zero zero) zero
            let rhs = cadd(d, p, sg_j, gj);
            let refl_rhs = d.lemma(p.equiv_refl, &[rhs]);
            let zz = cadd(d, p, zero_c, zero_c);
            d.lemma(
                p.le_congr,
                &[zz, zero_c, rhs, rhs, add_zero_proof, refl_rhs, combined],
            )
        },
        n,
    )
}

/// `le zero (add (sumRange (pow_fn x) (add m n)) (neg (sumRange (pow_fn x)
/// m)))` — the geometric tail is nonnegative. Reduces the tail to `sumRange
/// (shifted_fn m (pow_fn x)) n` via [`CRealPrelude::sum_range_split`] +
/// [`cancel_right`] (the group identity `(A+B)+(−A) ~ B` with `A := sumRange
/// f m`, `B := sumRange (shifted_fn m f) n`), then transports
/// [`geom_shifted_sum_nonneg`]'s conclusion across that `Equiv`.
fn geom_tail_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    h0: ExprId,
    m: ExprId,
    n: ExprId,
) -> ExprId {
    let f = pow_fn(d, p, x);
    let nat_add = d.prelude().add;
    let mn = d.const_app(nat_add, &[m, n]);
    let sum_f_mn = d.const_app(p.sum_range, &[f, mn]);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let neg_sum_f_m = cneg(d, p, sum_f_m);
    let tail = cadd(d, p, sum_f_mn, neg_sum_f_m);

    let g = shifted_fn(d, m, f);
    let sum_g_n = d.const_app(p.sum_range, &[g, n]);

    // split_proof : Equiv sum_f_mn (add sum_f_m sum_g_n)
    let split_proof = d.lemma(p.sum_range_split, &[f, m, n]);
    let refl_neg = d.lemma(p.equiv_refl, &[neg_sum_f_m]);
    let mid = cadd(d, p, sum_f_m, sum_g_n);
    let step1_target = cadd(d, p, mid, neg_sum_f_m);
    let step1 = d.lemma(
        p.add_congr,
        &[
            sum_f_mn,
            mid,
            neg_sum_f_m,
            neg_sum_f_m,
            split_proof,
            refl_neg,
        ],
    );
    // step1 : Equiv tail step1_target

    // cancel_proof : Equiv step1_target sum_g_n
    let cancel_proof = cancel_right(d, p, sum_f_m, sum_g_n);

    let tail_equiv_sum_g_n = d.lemma(
        p.equiv_trans,
        &[tail, step1_target, sum_g_n, step1, cancel_proof],
    );

    let nonneg_g_n = geom_shifted_sum_nonneg(d, p, x, h0, m, n);

    let zero_c = czero(d, p);
    let refl_zero = d.lemma(p.equiv_refl, &[zero_c]);
    let symm_te = d.lemma(p.equiv_symm, &[tail, sum_g_n, tail_equiv_sum_g_n]);
    d.lemma(
        p.le_congr,
        &[
            zero_c, zero_c, sum_g_n, tail, refl_zero, symm_te, nonneg_g_n,
        ],
    )
}

/// `CReal.geom_tail_within`. See the module documentation for the derivation
/// and — importantly — for what this theorem does **not** yet close.
fn declare_geom_tail_within(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let nat_add = d.prelude().add;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_x = cneg(d, p, x);
    let a = cadd(d, p, one, neg_x); // a = 1 - x
    let hyp_pos_bound = pos_bound_of(d, p, a, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mn = d.const_app(nat_add, &[m, n]);
    let f = pow_fn(d, p, x);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let sum_f_mn = d.const_app(p.sum_range, &[f, mn]);
    let neg_sum_f_m = cneg(d, p, sum_f_m);
    let tail = cadd(d, p, sum_f_mn, neg_sum_f_m);

    let pow_m = d.const_app(p.pow, &[x, m]);
    let inv_expr = cinv(d, p, a, k, h);
    let y = cmul(d, p, inv_expr, pow_m);

    let hyp0 = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, x)
    };

    // h_dom : le tail y
    let h_dom = d.lemma(p.geom_tail_bounded_div, &[x, h0, k, h, m, n]);

    // tail_nonneg : le zero tail
    let tail_nonneg = geom_tail_nonneg(d, p, x, h0, m, n);

    // y_nonneg : le zero y
    let inv_nonneg_fact = d.lemma(p.inv_nonneg, &[a, k, h]);
    let pow_nonneg_fact = d.lemma(p.pow_nonneg, &[x, h0, m]);
    let y_nonneg = d.lemma(
        p.mul_nonneg,
        &[inv_expr, pow_m, inv_nonneg_fact, pow_nonneg_fact],
    );

    // neg_tail_le_zero : le (neg tail) zero
    let neg_tail = cneg(d, p, tail);
    let zero_c = czero(d, p);
    let neg_le_neg_fact = d.lemma(p.neg_le_neg, &[zero_c, tail, tail_nonneg]);
    // neg_le_neg_fact : le (neg tail) (neg zero)
    let neg_zero_pf = neg_zero_equiv(d, p);
    let refl_neg_tail = d.lemma(p.equiv_refl, &[neg_tail]);
    let neg_zero_c = cneg(d, p, zero_c);
    let neg_tail_le_zero = d.lemma(
        p.le_congr,
        &[
            neg_tail,
            neg_tail,
            neg_zero_c,
            zero_c,
            refl_neg_tail,
            neg_zero_pf,
            neg_le_neg_fact,
        ],
    );

    // neg_tail_le_y : le (neg tail) y
    let neg_tail_le_y = d.lemma(
        p.le_trans,
        &[neg_tail, zero_c, y, neg_tail_le_zero, y_nonneg],
    );

    // Apply both real-valued `le` facts directly at the tail's own canonical
    // index `mn` -- `CReal.le` is a `Definition` (`∀ n, seq x n - seq y n ≤
    // 2/(n+1)`), so `.apply(_, &[mn])` unfolds it to the per-index `Rat.le`
    // fact, exactly as `series.rs::declare_sum_range_tail_within` does for
    // its own `r1`/`r2`.
    let h1 = d.apply(h_dom, &[mn]);
    let h2 = d.apply(neg_tail_le_y, &[mn]);

    let u = sample(d, p, tail, mn);
    let v = sample(d, p, y, mn);
    let w = div_succ(d, p, 2, mn);

    let value_body = within_of_tail_le(d, p, u, v, w, h1, h2);

    let ty = {
        let vw = radd(d, v, w);
        let claim = within(d, p, u, vw);
        let inner = d.pi_fv(n_fv, nat, claim);
        let with_m = d.pi_fv(m_fv, nat, inner);
        // `h_fv` escapes into `with_m` through `y` (via `inv_expr`), so this
        // Pi must be genuinely dependent (`pi_fv`), not `d.arrow` -- the same
        // trap `geom_tail_bounded_div`'s own `ty` names.
        let with_h = d.pi_fv(h_fv, hyp_pos_bound, with_m);
        let with_k = d.pi_fv(k_fv, nat, with_h);
        let with_h0 = d.arrow(hyp0, with_k);
        d.pi_fv(x_fv, carrier, with_h0)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, value_body);
        let with_m = d.lam_fv(m_fv, nat, inner);
        let with_h = d.lam_fv(h_fv, hyp_pos_bound, with_m);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_h0 = d.lam_fv(h0_fv, hyp0, with_k);
        d.lam_fv(x_fv, carrier, with_h0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_tail_within,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `geom_tail_within_le` ---------------------------------------------------

/// `CReal.geom_tail_within_le`. See the field documentation
/// ([`super::CRealPrelude::geom_tail_within_le`]) for the statement, and this
/// module's documentation for what it does and does not close.
///
/// Verbatim in *technique* to `series.rs::declare_sum_range_tail_within_le`
/// (private there, so reproduced rather than imported): `Nat.le_dest a b hle
/// : Exists (fun kk => Eq (add a kk) b)`, apply [`declare_geom_tail_within`]
/// at `(a, kk)` to land exactly this theorem's target *shape* but indexed at
/// `add a kk`, then [`nat_rewrite_prop`] carries every occurrence of that
/// shared index over to `b` along the witness, and [`exists_elim`]
/// discharges the existential.
fn declare_geom_tail_within_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let nat_add = d.prelude().add;
    let nat_le_dest = d.prelude().le_dest;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let bk_fv = d.fresh_fvar();
    let bk = d.kernel().fvar(bk_fv);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_x = cneg(d, p, x);
    let a_real = cadd(d, p, one, neg_x); // a_real = 1 - x
    let hyp_pos_bound = pos_bound_of(d, p, a_real, bk);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hyp0 = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, x)
    };

    let f = pow_fn(d, p, x);
    let sum_f_a = d.const_app(p.sum_range, &[f, a]);
    let neg_sum_f_a = cneg(d, p, sum_f_a);
    let pow_a = d.const_app(p.pow, &[x, a]);
    let inv_expr = cinv(d, p, a_real, bk, h);
    let y_a = cmul(d, p, inv_expr, pow_a);

    // `target_at(idx)`: the claim with the shared index left as `idx`, so it
    // reads directly off `declare_geom_tail_within`'s own conclusion shape at
    // `idx := add a kk`, and is this theorem's conclusion at `idx := b`.
    let target_at = |d: &mut IntDev<'_>, idx: ExprId| -> ExprId {
        let sum_f_idx = d.const_app(p.sum_range, &[f, idx]);
        let tail_idx = cadd(d, p, sum_f_idx, neg_sum_f_a);
        let u = sample(d, p, tail_idx, idx);
        let v = sample(d, p, y_a, idx);
        let w = div_succ(d, p, 2, idx);
        let vw = radd(d, v, w);
        within(d, p, u, vw)
    };
    let target = target_at(d, b);

    let hle_ty = d.le(a, b);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    // pred := λ kk, Eq Nat (add a kk) b.
    let pred = {
        let kk_fv = d.fresh_fvar();
        let kk = d.kernel().fvar(kk_fv);
        let sum = d.const_app(nat_add, &[a, kk]);
        let body = d.eq(sum, b);
        d.lam_fv(kk_fv, nat, body)
    };

    let represented = d.const_app(nat_le_dest, &[a, b, hle]);

    let minor = {
        let kk_fv = d.fresh_fvar();
        let kk = d.kernel().fvar(kk_fv);
        let a_plus_kk = d.const_app(nat_add, &[a, kk]);
        let e_ty = d.eq(a_plus_kk, b);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        // body_at_akk : target_at(add a kk) -- exactly
        // `geom_tail_within x h0 bk h a kk`'s own conclusion.
        let body_at_akk = d.lemma(p.geom_tail_within, &[x, h0, bk, h, a, kk]);
        let rewritten = nat_rewrite_prop(d, a_plus_kk, b, e, body_at_akk, &|d, t| target_at(d, t));

        let with_e = d.lam_fv(e_fv, e_ty, rewritten);
        d.lam_fv(kk_fv, nat, with_e)
    };

    let proof_body = exists_elim(d, pred, target, represented, minor);

    let ty = {
        let after_hle = d.arrow(hle_ty, target);
        let over_b = d.pi_fv(b_fv, nat, after_hle);
        let over_a = d.pi_fv(a_fv, nat, over_b);
        // `h_fv` escapes into `over_a` through `y_a` (via `inv_expr`), so this
        // Pi must be genuinely dependent (`pi_fv`), not `d.arrow` -- the same
        // trap `geom_tail_bounded_div`'s own `ty` names.
        let with_h = d.pi_fv(h_fv, hyp_pos_bound, over_a);
        let with_bk = d.pi_fv(bk_fv, nat, with_h);
        let with_h0 = d.arrow(hyp0, with_bk);
        d.pi_fv(x_fv, carrier, with_h0)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, proof_body);
        let over_b = d.lam_fv(b_fv, nat, with_hle);
        let over_a = d.lam_fv(a_fv, nat, over_b);
        let with_h = d.lam_fv(h_fv, hyp_pos_bound, over_a);
        let with_bk = d.lam_fv(bk_fv, nat, with_h);
        let with_h0 = d.lam_fv(h0_fv, hyp0, with_bk);
        d.lam_fv(x_fv, carrier, with_h0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_tail_within_le,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `geom_pair_within` ------------------------------------------------------

/// From `Within (a-b) q`, derive `Within (b-a) q` via `Rat.neg_sub` and
/// `Rat.bounds_neg`. Verbatim copy of `series.rs::within_symm` (private
/// there): the generic "swap the two sides of a `Within` difference" helper.
fn within_symm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    q: ExprId,
    pab: ExprId,
) -> ExprId {
    let rat = p.rat;
    let ab = rsub(d, rat, a, b);
    let (lower, upper) = halves(d, p, ab, q, pab);
    let neg_within = d.lemma(rat.bounds_neg, &[ab, q, lower, upper]);
    let neg_ab = rneg(d, ab);
    let ba = rsub(d, rat, b, a);
    let eq = d.lemma(rat.neg_sub, &[a, b]);
    rat_eq_rewrite(d, neg_ab, ba, eq, neg_within, &|d, t| within(d, p, t, q))
}

/// From `Within (x−y) bxy`, `Within (y−z) byz`, `Within (z−w) bzw`, derive
/// `Within (x−w) ((bxy+byz)+bzw)`. Verbatim copy of `series.rs::chain_within3`
/// (private there): two applications of `Rat.sub_add_sub`.
#[allow(clippy::too_many_arguments)]
fn chain_within3(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    w: ExprId,
    bxy: ExprId,
    byz: ExprId,
    bzw: ExprId,
    pxy: ExprId,
    pyz: ExprId,
    pzw: ExprId,
) -> ExprId {
    let rat = p.rat;

    // (x-y)+(y-z) ~ x-z, bound bxy+byz.
    let xy = rsub(d, rat, x, y);
    let yz = rsub(d, rat, y, z);
    let (lxy, rxy) = halves(d, p, xy, bxy, pxy);
    let (lyz, ryz) = halves(d, p, yz, byz, pyz);
    let combined1 = d.lemma(rat.bounds_add, &[xy, bxy, yz, byz, lxy, rxy, lyz, ryz]);
    let xy_plus_yz = radd(d, xy, yz);
    let xz = rsub(d, rat, x, z);
    let fuse1 = d.lemma(rat.sub_add_sub, &[x, y, z]); // Eq ((x-y)+(y-z)) (x-z)
    let bound1 = radd(d, bxy, byz);
    let at_xz = rat_eq_rewrite(d, xy_plus_yz, xz, fuse1, combined1, &|d, t| {
        within(d, p, t, bound1)
    });

    // (x-z)+(z-w) ~ x-w, bound (bxy+byz)+bzw.
    let (lxz, rxz) = halves(d, p, xz, bound1, at_xz);
    let zw = rsub(d, rat, z, w);
    let (lzw, rzw) = halves(d, p, zw, bzw, pzw);
    let combined2 = d.lemma(rat.bounds_add, &[xz, bound1, zw, bzw, lxz, rxz, lzw, rzw]);
    let xz_plus_zw = radd(d, xz, zw);
    let xw = rsub(d, rat, x, w);
    let fuse2 = d.lemma(rat.sub_add_sub, &[x, z, w]); // Eq ((x-z)+(z-w)) (x-w)
    let bound2 = radd(d, bound1, bzw);
    rat_eq_rewrite(d, xz_plus_zw, xw, fuse2, combined2, &|d, t| {
        within(d, p, t, bound2)
    })
}

/// `CReal.geom_pair_within`. See the field documentation
/// ([`super::CRealPrelude::geom_pair_within`]) and this module's own
/// documentation for exactly what this theorem does and does not close.
///
/// Chains four points `Y → X → W → Z` via [`chain_within3`], mirroring
/// `series.rs::dominated_canonical_at`'s own construction (private there) —
/// **except** the middle leg (`X − W`, defeq to
/// [`declare_geom_tail_within_le`]'s own conclusion at `(a, b)`, by the same
/// ι/β argument that theorem's own doc comment gives for
/// `geom_tail_within`) needs no separately-witnessed `Cauchy` hypothesis,
/// and the two outer legs are [`CRealPrelude::regular`] applied directly to
/// `sumRange f b` / `sumRange f a` themselves (true of any `CReal`, no
/// domination needed).
fn declare_geom_pair_within(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let bk_fv = d.fresh_fvar();
    let bk = d.kernel().fvar(bk_fv);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_x = cneg(d, p, x);
    let a_real = cadd(d, p, one, neg_x); // a_real = 1 - x
    let hyp_pos_bound = pos_bound_of(d, p, a_real, bk);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hyp0 = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, x)
    };
    let hle_ty = d.le(a, b);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let f = pow_fn(d, p, x);
    let sum_f_b = d.const_app(p.sum_range, &[f, b]);
    let sum_f_a = d.const_app(p.sum_range, &[f, a]);
    let t = shift(d, b);

    let y_pt = sample(d, p, sum_f_b, b);
    let x_pt = sample(d, p, sum_f_b, t);
    let w_pt = sample(d, p, sum_f_a, t);
    let z_pt = sample(d, p, sum_f_a, a);

    // tail_le : Within (seq (add (sumRange f b) (neg (sumRange f a))) b)
    //                  (v+w) -- defeq to Within (x_pt - w_pt) (v+w).
    let tail_le = d.lemma(p.geom_tail_within_le, &[x, h0, bk, h, a, b, hle]);

    let bxy = modulus(d, p, t, b);
    let bzw = modulus(d, p, a, t);
    let pow_a = d.const_app(p.pow, &[x, a]);
    let inv_expr = cinv(d, p, a_real, bk, h);
    let y_a = cmul(d, p, inv_expr, pow_a);
    let v = sample(d, p, y_a, b);
    let w = div_succ(d, p, 2, b);
    let byz = radd(d, v, w);

    // p_yx : Within (y_pt - x_pt) bxy, from CReal.regular reversed.
    let reg1 = d.lemma(p.regular, &[sum_f_b, t, b]);
    let p_yx = within_symm(d, p, x_pt, y_pt, bxy, reg1);

    // p_wz : Within (w_pt - z_pt) bzw, from CReal.regular reversed.
    let reg2 = d.lemma(p.regular, &[sum_f_a, a, t]);
    let p_wz = within_symm(d, p, z_pt, w_pt, bzw, reg2);

    let value_body = chain_within3(
        d, p, y_pt, x_pt, w_pt, z_pt, bxy, byz, bzw, p_yx, tail_le, p_wz,
    );

    let bxy_byz = radd(d, bxy, byz);
    let total = radd(d, bxy_byz, bzw);
    let diff = rsub(d, p.rat, y_pt, z_pt);

    let ty = {
        let claim = within(d, p, diff, total);
        let after_hle = d.arrow(hle_ty, claim);
        let over_b = d.pi_fv(b_fv, nat, after_hle);
        let over_a = d.pi_fv(a_fv, nat, over_b);
        // `h_fv` escapes into `over_a` through `y_a`/`inv_expr`, so this Pi
        // must be genuinely dependent (`pi_fv`), not `d.arrow`.
        let with_h = d.pi_fv(h_fv, hyp_pos_bound, over_a);
        let with_bk = d.pi_fv(bk_fv, nat, with_h);
        let with_h0 = d.arrow(hyp0, with_bk);
        d.pi_fv(x_fv, carrier, with_h0)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, value_body);
        let over_b = d.lam_fv(b_fv, nat, with_hle);
        let over_a = d.lam_fv(a_fv, nat, over_b);
        let with_h = d.lam_fv(h_fv, hyp_pos_bound, over_a);
        let with_bk = d.lam_fv(bk_fv, nat, with_h);
        let with_h0 = d.lam_fv(h0_fv, hyp0, with_bk);
        d.lam_fv(x_fv, carrier, with_h0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_pair_within,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.geom_tail_bounded_div`, `CReal.geom_tail_within`,
/// `CReal.geom_tail_within_le`, and `CReal.geom_pair_within`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_geometric(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_geom_tail_bounded_div(d, p)?;
    declare_geom_tail_within(d, p)?;
    declare_geom_tail_within_le(d, p)?;
    declare_geom_pair_within(d, p)?;
    declare_pow_le_pow_of_base_le(d, p)?;
    declare_of_rat_pow(d, p)?;
    declare_pow_half_le_nat_div_succ(d, p)?;
    declare_pow_le_nat_div_succ_of_lt(d, p)?;
    declare_pow_le_nat_div_succ_of_gap(d, p)?;
    declare_ratio_decay_bound(d, p)?;
    declare_inv_le_of_pos_bound(d, p)?;
    declare_geom_y_bound(d, p)?;
    declare_geom_y_bound_raw(d, p)
}

// --- `pow_le_pow_of_base_le` -------------------------------------------------

/// `CReal.pow_le_pow_of_base_le`. See the field documentation
/// ([`super::CRealPrelude::pow_le_pow_of_base_le`]) for the statement and the
/// derivation.
fn declare_pow_le_pow_of_base_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let px = d.const_app(p.pow, &[x, v]);
        let py = d.const_app(p.pow, &[y, v]);
        cle(d, p, px, py)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    // h0y : le zero y, from le zero x and le x y.
    let h0y = {
        let zero_c = czero(d, p);
        d.lemma(p.le_trans, &[zero_c, x, y, h0, hxy])
    };

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let one = d.kernel().const_(p.one, vec![]);
            d.lemma(p.le_refl, &[one])
        },
        &|d, j, ih| {
            let px_j = d.const_app(p.pow, &[x, j]);
            let py_j = d.const_app(p.pow, &[y, j]);

            // raw1 : le (mul x px_j) (mul x py_j), from 0 ≤ x and ih.
            let raw1 = d.lemma(p.mul_le_mul_of_nonneg_left, &[x, px_j, py_j, h0, ih]);
            let x_pxj = cmul(d, p, x, px_j);
            let x_pyj = cmul(d, p, x, py_j);
            let pxj_x = cmul(d, p, px_j, x);
            let pyj_x = cmul(d, p, py_j, x);
            let comm_left = d.lemma(p.mul_comm, &[x, px_j]); // Equiv x_pxj pxj_x
            let comm_right = d.lemma(p.mul_comm, &[x, py_j]); // Equiv x_pyj pyj_x
            // term1 : le pxj_x pyj_x
            let term1 = d.lemma(
                p.le_congr,
                &[x_pxj, pxj_x, x_pyj, pyj_x, comm_left, comm_right, raw1],
            );

            // step2 : le (mul py_j x) (mul py_j y), from 0 ≤ py_j and x ≤ y.
            let py_j_nonneg = d.lemma(p.pow_nonneg, &[y, h0y, j]);
            let step2 = d.lemma(p.mul_le_mul_of_nonneg_left, &[py_j, x, y, py_j_nonneg, hxy]);
            let pyj_y = cmul(d, p, py_j, y);

            // final : le pxj_x pyj_y -- defeq to le (pow x (succ j)) (pow y (succ j)).
            d.lemma(p.le_trans, &[pxj_x, pyj_x, pyj_y, term1, step2])
        },
        n,
    );

    let hyp0 = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, x)
    };
    let hyp_xy = cle(d, p, x, y);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_hxy = d.arrow(hyp_xy, inner);
        let with_h0 = d.arrow(hyp0, with_hxy);
        let with_y = d.pi_fv(y_fv, carrier, with_h0);
        d.pi_fv(x_fv, carrier, with_y)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_hxy = d.lam_fv(hxy_fv, hyp_xy, inner);
        let with_h0 = d.lam_fv(h0_fv, hyp0, with_hxy);
        let with_y = d.lam_fv(y_fv, carrier, with_h0);
        d.lam_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_le_pow_of_base_le,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.ofRat_pow`, and the concrete geometric-decay-dominates-harmonic-rate
// bound at base `1/2` it unlocks (`CReal.pow_half_le_natDivSucc`).
//
// The three private helpers immediately below are verbatim reproductions of
// sibling modules' own private helpers, per this file's established
// precedent (`cancel_left` above is `cancellation.rs::cancel_left`;
// `chain_within3`/`within_of_tail_le` earlier in this file are
// `series.rs`'s own): `l_term`/`one_le_l` are
// `rat_prelude/bernoulli.rs::l_term`/`one_le_l`, and `ne_zero_of_pos` is
// `rat_prelude/probability.rs::ne_zero_of_pos`. None of the three is `pub`
// in its home module, and none of those files is in this slice's edit
// boundary.
// ---------------------------------------------------------------------------

/// `L t n`, built as `Nat.rec (fun _ => Rat) Rat.one (fun _ ih => Rat.add ih
/// t) n` — `L t 0 ≡ 1`, `L t (succ j) ≡ L t j + t`. Verbatim reproduction of
/// `rat_prelude/bernoulli.rs::l_term` (private there).
fn l_term(d: &mut IntDev<'_>, p: RatPrelude, t: ExprId, n: ExprId) -> ExprId {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();

    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = rone(d, p);
    let minor_succ = {
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let body = radd(d, ih, t);
        let inner = d.lam_fv(ih_fv, carrier, body);
        let j_fv = d.fresh_fvar();
        d.lam_fv(j_fv, nat, inner)
    };
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    d.apply(rec, &[motive, minor_zero, minor_succ, n])
}

/// `one_le_l t h n : Rat.le Rat.one (L t n)`, given `h : Rat.le Rat.zero t`.
/// Verbatim reproduction of `rat_prelude/bernoulli.rs::one_le_l` (private
/// there).
fn one_le_l(d: &mut IntDev<'_>, p: RatPrelude, t: ExprId, h: ExprId, n: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let one = rone(d, p);
        let lx = l_term(d, p, t, x);
        rle(d, p, one, lx)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let one = rone(d, p);
        d.lemma(p.le_refl, &[one])
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let one = rone(d, p);
        let zero = rzero(d, p);
        let lj = l_term(d, p, t, j);
        let sum_le = d.lemma(p.add_le_add, &[one, lj, zero, t, ih, h]);
        let one_plus_zero = radd(d, one, zero);
        let add_zero_eq = d.lemma(p.add_zero, &[one]);
        let target_rhs = radd(d, lj, t);
        rat_eq_rewrite(d, one_plus_zero, one, add_zero_eq, sum_le, &|d, x| {
            rle(d, p, x, target_rhs)
        })
    };
    d.induct(&motive, &base, &step, n)
}

/// `Not (Eq Rat val zero)`, from `lt zero val`. Verbatim reproduction of
/// `rat_prelude/probability.rs::ne_zero_of_pos` (private there).
fn ne_zero_of_pos(d: &mut IntDev<'_>, p: RatPrelude, val: ExprId, h_pos: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let eq_ty = req(d, val, zero_r);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);
    let rewritten = rat_eq_rewrite(d, val, zero_r, heq, h_pos, &|d, t| rlt(d, p, zero_r, t));
    let irrefl = d.lemma(p.lt_irrefl, &[zero_r]);
    let false_proof = d.apply(irrefl, &[rewritten]);
    d.lam_fv(heq_fv, eq_ty, false_proof)
}

/// `Eq Rat (L Rat.one n) (natDivSucc (Nat.succ n) 0)` — the harmonic
/// companion sequence at `t := 1` is exactly the whole-number embedding
/// `n+1`. Induction on `n`. The step needs only
/// [`crate::rat_prelude::RatPrelude::nat_div_succ_add`] (at `(succ j, 1, 0)`
/// — `Nat.add(succ j, 1)` reduces directly since `Nat.add` recurses on its
/// RIGHT argument and the right argument here is the literal `1`, never the
/// stuck `1 + symbolic` shape) and
/// [`super::CRealPrelude::rat_unit_eq_one`] (`natDivSucc 1 0 = Rat.one`) to
/// rewrite `Rat.one` into `natDivSucc 1 0` before fusing.
fn l_one_eq_embed(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let one_r = rone(d, rat);

    let motive = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let lk = l_term(d, rat, one_r, k);
        let succ_k = d.succ(k);
        let embedded = d.const_app(rat.nat_div_succ, &[succ_k, zero_nat]);
        req(d, lk, embedded)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
        let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
        rsymm(d, unit, one_r, unit_eq_one)
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let lj = l_term(d, rat, one_r, j);
        let succ_j = d.succ(j);
        let embedded_j = d.const_app(rat.nat_div_succ, &[succ_j, zero_nat]);
        let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
        let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
        let one_eq_unit = rsymm(d, unit, one_r, unit_eq_one);

        let step1 = rcongr(d, lj, embedded_j, ih, &|d, y| radd(d, y, one_r));
        let step2 = rcongr(d, one_r, unit, one_eq_unit, &|d, y| radd(d, embedded_j, y));
        let step3 = d.lemma(rat.nat_div_succ_add, &[succ_j, one_nat, zero_nat]);

        let succ_succ_j = d.succ(succ_j);
        let target = d.const_app(rat.nat_div_succ, &[succ_succ_j, zero_nat]);
        let lj_plus_one = radd(d, lj, one_r);
        let embedded_j_plus_one = radd(d, embedded_j, one_r);
        let embedded_j_plus_unit = radd(d, embedded_j, unit);
        let (_, proof) = rchain(
            d,
            lj_plus_one,
            &[
                (embedded_j_plus_one, step1),
                (embedded_j_plus_unit, step2),
                (target, step3),
            ],
        );
        proof
    };
    d.induct(&motive, &base, &step, n)
}

/// From `A ≥ 0`, `A·d = 1`, and `A·y ≤ 1`, derive `y ≤ d` — cancelling the
/// positive factor `A` without ever forming `A⁻¹`, matching
/// `bernoulli_harmonic_bound`'s own design (`rat_prelude/bernoulli.rs`'s
/// module doc: "avoiding `Rat.inv` on either side"). `Rat.le_total` supplies
/// the case split (order is decidable over `ℚ`, no classical logic needed);
/// the `d ≤ y` branch turns `A·d ≤ A·y` (from
/// [`crate::rat_prelude::RatPrelude::mul_le_mul_of_nonneg_left`]) plus `A·y ≤
/// 1 = A·d` into `A·d = A·y` via
/// [`crate::rat_prelude::RatPrelude::le_antisymm`], then cancels `A` via
/// [`crate::rat_prelude::RatPrelude::mul_left_cancel_of_ne_zero`] (needing `A
/// ≠ 0`, supplied by the caller via [`ne_zero_of_pos`]).
#[allow(clippy::too_many_arguments)]
fn cancel_pos_mul_left(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    a_val: ExprId,
    y: ExprId,
    dd: ExprId,
    h_nonneg_a: ExprId,
    h_eq_ad: ExprId,
    h_le_ay: ExprId,
    h_a_ne_zero: ExprId,
) -> ExprId {
    let one = rone(d, rat);
    let tot = d.lemma(rat.le_total, &[y, dd]);
    let left_ty = rle(d, rat, y, dd);
    let right_ty = rle(d, rat, dd, y);
    d.or_elim(left_ty, right_ty, left_ty, tot, &|_d, h| h, &|d, h| {
        let mul_ad = rmul(d, a_val, dd);
        let mul_ay = rmul(d, a_val, y);
        let step1 = d.lemma(
            rat.mul_le_mul_of_nonneg_left,
            &[a_val, dd, y, h_nonneg_a, h],
        );
        let step1b = rat_eq_rewrite(d, mul_ad, one, h_eq_ad, step1, &|d, t| {
            rle(d, rat, t, mul_ay)
        });
        let eq_one_ay = d.lemma(rat.le_antisymm, &[one, mul_ay, step1b, h_le_ay]);
        let eq_ad_ay = rtrans(d, mul_ad, one, mul_ay, h_eq_ad, eq_one_ay);
        let eq_d_y = d.lemma(
            rat.mul_left_cancel_of_ne_zero,
            &[a_val, dd, y, h_a_ne_zero, eq_ad_ay],
        );
        let eq_y_d = rsymm(d, dd, y, eq_d_y);
        let refl_y = d.lemma(rat.le_refl, &[y]);
        rat_eq_rewrite(d, y, dd, eq_y_d, refl_y, &|d, t| rle(d, rat, y, t))
    })
}

/// `Rat.le (Rat.pow (natDivSucc 1 1) n) (Rat.natDivSucc 1 n)` — the concrete
/// harmonic bound at base `1/2`. Chains
/// [`crate::rat_prelude::RatPrelude::bernoulli_harmonic_bound`] (at `x :=
/// 1/2`, `t := 1`) with [`cancel_pos_mul_left`] to strip the `L 1 n` factor,
/// using [`l_one_eq_embed`] to identify it with the whole-number embedding
/// `natDivSucc (n+1) 0` and
/// [`crate::rat_prelude::RatPrelude::nat_div_succ_mul`] +
/// [`crate::nat_prelude::NatPrelude::mul_one`] to show that embedding times
/// `natDivSucc 1 n` is exactly `natDivSucc (n+1) n`, closed by
/// [`crate::rat_prelude::RatPrelude::nat_div_succ_scale`] (at `c := n`, its
/// own `m := 0`) plus [`crate::nat_prelude::NatPrelude::zero_add`] (the one
/// place this proof needs `0 + n = n` for a symbolic `n`, since
/// `nat_div_succ_scale`'s index is `(c+1)·0 + c` and `Nat.add` recurses on
/// its right argument).
fn rat_pow_half_le_nat_div_succ(d: &mut IntDev<'_>, p: CRealPrelude, mm: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let one_r = rone(d, rat);
    let zero_r = rzero(d, rat);
    let half = div_succ(d, p, 1, one_nat);

    // hx : 0 ≤ half.
    let hx = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, one_nat]);
    // ht : 0 ≤ one.
    let zlo = d.lemma(rat.zero_lt_one, &[]);
    let ht = d.lemma(rat.le_of_lt, &[zero_r, one_r, zlo]);

    // hxt : half * (one + one) ≤ one, from the equality half*2 = 1.
    let hxt = {
        let two_sum = radd(d, one_r, one_r);
        let mul_expr = rmul(d, half, two_sum);
        let mul_half_one = rmul(d, half, one_r);

        let ld = d.lemma(rat.left_distrib, &[half, one_r, one_r]);
        let mo = d.lemma(rat.mul_one, &[half]);
        let step1 = rcongr(d, mul_half_one, half, mo, &|d, y| radd(d, y, mul_half_one));
        let step2 = rcongr(d, mul_half_one, half, mo, &|d, y| radd(d, half, y));

        let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
        let two_nat = d.num(2);
        let two_one = d.const_app(rat.nat_div_succ, &[two_nat, one_nat]);
        let e1 = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, one_nat]);
        let e2 = d.lemma(rat.nat_div_succ_halve, &[zero_nat]);
        let e3 = d.lemma(p.rat_unit_eq_one, &[]);

        let sum_half_half = radd(d, half, half);
        let sum_mul_half_one = radd(d, mul_half_one, mul_half_one);
        let sum_half_mul_half_one = radd(d, half, mul_half_one);

        let (_, chain_proof) = rchain(
            d,
            mul_expr,
            &[
                (sum_mul_half_one, ld),
                (sum_half_mul_half_one, step1),
                (sum_half_half, step2),
                (two_one, e1),
                (unit, e2),
                (one_r, e3),
            ],
        );
        let sym = rsymm(d, mul_expr, one_r, chain_proof);
        let refl_one = d.lemma(rat.le_refl, &[one_r]);
        rat_eq_rewrite(d, one_r, mul_expr, sym, refl_one, &|d, t| {
            rle(d, rat, t, one_r)
        })
    };

    // bound : le (mul (L one mm) (pow half mm)) one.
    let bound = d.lemma(
        rat.bernoulli_harmonic_bound,
        &[half, one_r, hx, ht, hxt, mm],
    );

    let l_mm = l_term(d, rat, one_r, mm);
    let pow_mm = rpow(d, rat, half, mm);
    let nat_div_1_mm = div_succ(d, p, 1, mm);

    // h_eq : mul (L one mm) (natDivSucc 1 mm) = one.
    let h_eq = {
        let succ_mm = d.succ(mm);
        let l_eq = l_one_eq_embed(d, p, mm);
        let embedded_mm = d.const_app(rat.nat_div_succ, &[succ_mm, zero_nat]);

        let step_a = rcongr(d, l_mm, embedded_mm, l_eq, &|d, y| rmul(d, y, nat_div_1_mm));
        let step_b = d.lemma(rat.nat_div_succ_mul, &[succ_mm, one_nat, mm]);

        let mul_one_name = d.prelude().mul_one;
        let mul_one_h = d.lemma(mul_one_name, &[succ_mm]);
        let mul_succ_mm_one = NatOps::mul(d, succ_mm, one_nat);
        let step_c = nat_eq_to_rat(d, mul_succ_mm_one, succ_mm, mul_one_h, &|d, k| {
            d.const_app(rat.nat_div_succ, &[k, mm])
        });

        // x0 : natDivSucc (succ mm) mm = one, via nat_div_succ_scale(mm, 0)
        // plus Nat.zero_add(mm).
        let x0 = {
            let zero_add_name = d.prelude().zero_add;
            let zero_add_h = d.lemma(zero_add_name, &[mm]);
            let a_idx = NatOps::add(d, zero_nat, mm);
            let raw = d.lemma(rat.nat_div_succ_scale, &[mm, zero_nat]);
            let natdiv_1_0 = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
            let natdiv_succmm_aidx = d.const_app(rat.nat_div_succ, &[succ_mm, a_idx]);
            let natdiv_succmm_mm = d.const_app(rat.nat_div_succ, &[succ_mm, mm]);
            let step_idx = nat_eq_to_rat(d, a_idx, mm, zero_add_h, &|d, k| {
                d.const_app(rat.nat_div_succ, &[succ_mm, k])
            });
            let step_idx_symm = rsymm(d, natdiv_succmm_aidx, natdiv_succmm_mm, step_idx);
            let x0_mid = rtrans(
                d,
                natdiv_succmm_mm,
                natdiv_succmm_aidx,
                natdiv_1_0,
                step_idx_symm,
                raw,
            );
            let e3 = d.lemma(p.rat_unit_eq_one, &[]);
            rtrans(d, natdiv_succmm_mm, natdiv_1_0, one_r, x0_mid, e3)
        };

        let mul_lmm_nd = rmul(d, l_mm, nat_div_1_mm);
        let mul_embedded_nd = rmul(d, embedded_mm, nat_div_1_mm);
        let natdiv_mul_one = d.const_app(rat.nat_div_succ, &[mul_succ_mm_one, mm]);
        let natdiv_succmm_mm2 = d.const_app(rat.nat_div_succ, &[succ_mm, mm]);
        let (_, proof) = rchain(
            d,
            mul_lmm_nd,
            &[
                (mul_embedded_nd, step_a),
                (natdiv_mul_one, step_b),
                (natdiv_succmm_mm2, step_c),
                (one_r, x0),
            ],
        );
        proof
    };

    // h_nonneg : 0 ≤ L one mm.
    let h_one_le_l = one_le_l(d, rat, one_r, ht, mm);
    let h_nonneg = d.lemma(rat.le_trans, &[zero_r, one_r, l_mm, ht, h_one_le_l]);

    // h_ne_zero : L one mm ≠ 0, from 0 < L one mm.
    let lt_zero_l = d.lemma(rat.lt_of_lt_of_le, &[zero_r, one_r, l_mm, zlo, h_one_le_l]);
    let h_ne_zero = ne_zero_of_pos(d, rat, l_mm, lt_zero_l);

    cancel_pos_mul_left(
        d,
        rat,
        l_mm,
        pow_mm,
        nat_div_1_mm,
        h_nonneg,
        h_eq,
        bound,
        h_ne_zero,
    )
}

/// `CReal.ofRat_pow : ∀ q n, Equiv (pow (ofRat q) n) (ofRat (Rat.pow q n))`.
///
/// Induction on `n`. See the module documentation for the field this
/// declares ([`CRealPrelude::of_rat_pow`]) for why neither `pow_zero` nor
/// `pow_succ` unfolding is needed.
fn declare_of_rat_pow(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let rat_carrier = rat_ty(d);
    let nat = d.nat_ty();

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let x = embed(d, p, q);

    let motive = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let lhs = d.const_app(p.pow, &[x, k]);
        let rpow_qk = rpow(d, rat, q, k);
        let rhs = embed(d, p, rpow_qk);
        equiv(d, p, lhs, rhs)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let one = d.kernel().const_(p.one, vec![]);
        d.lemma(p.equiv_refl, &[one])
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let pow_xj = d.const_app(p.pow, &[x, j]);
        let rpow_qj = rpow(d, rat, q, j);
        let embed_rpow_qj = embed(d, p, rpow_qj);
        let refl_x = d.lemma(p.equiv_refl, &[x]);
        let step1 = d.lemma(p.mul_congr, &[pow_xj, embed_rpow_qj, x, x, ih, refl_x]);
        let step2 = d.lemma(p.of_rat_mul, &[rpow_qj, q]);

        let mul_pow_xj_x = d.const_app(p.mul, &[pow_xj, x]);
        let mul_embed_x = d.const_app(p.mul, &[embed_rpow_qj, x]);
        let scaled = rmul(d, rpow_qj, q);
        let embed_scaled = embed(d, p, scaled);
        d.lemma(
            p.equiv_trans,
            &[mul_pow_xj_x, mul_embed_x, embed_scaled, step1, step2],
        )
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof_n = d.induct(&motive, &base, &step, n);
    let stmt_n = motive(d, n);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt_n);
        d.pi_fv(q_fv, rat_carrier, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof_n);
        d.lam_fv(q_fv, rat_carrier, with_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_rat_pow,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.pow_half_le_natDivSucc : ∀ n, le (pow (ofRat (natDivSucc 1 1)) n)
/// (ofRat (natDivSucc 1 n))`. See [`CRealPrelude::pow_half_le_nat_div_succ`]
/// for the derivation.
fn declare_pow_half_le_nat_div_succ(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let one_nat = d.num(1);
    let half_rat = div_succ(d, p, 1, one_nat);
    let half_creal = embed(d, p, half_rat);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let rat_le_proof = rat_pow_half_le_nat_div_succ(d, p, n);

    let rpow_n = rpow(d, rat, half_rat, n);
    let nat_div_1_n = div_succ(d, p, 1, n);
    let ofrat_rpow_n = embed(d, p, rpow_n);
    let ofrat_natdiv_n = embed(d, p, nat_div_1_n);

    let of_rat_le_proof = d.lemma(p.of_rat_le, &[rpow_n, nat_div_1_n, rat_le_proof]);
    let of_rat_pow_proof = d.lemma(p.of_rat_pow, &[half_rat, n]);

    let pow_half_n = d.const_app(p.pow, &[half_creal, n]);
    let hab = d.lemma(p.equiv_symm, &[pow_half_n, ofrat_rpow_n, of_rat_pow_proof]);
    let hce = d.lemma(p.equiv_refl, &[ofrat_natdiv_n]);

    let final_proof = d.lemma(
        p.le_congr,
        &[
            ofrat_rpow_n,
            pow_half_n,
            ofrat_natdiv_n,
            ofrat_natdiv_n,
            hab,
            hce,
            of_rat_le_proof,
        ],
    );

    let value = d.lam_fv(n_fv, nat, final_proof);
    let ty = {
        let stmt = cle(d, p, pow_half_n, ofrat_natdiv_n);
        d.pi_fv(n_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_half_le_nat_div_succ,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.pow_le_natDivSucc_of_lt` -- geometric decay at ANY ratio `0 ≤ x < 1`
// dominates some harmonic rate, entirely `CReal.inv`/`PosBound`-free. See
// the field documentation (`CRealPrelude::pow_le_nat_div_succ_of_lt`).
//
// The rational-level `Rat.bernoulli_harmonic_bound` cannot be reused directly
// here: bridging it back across a `CReal.pow` SAMPLE is exactly the gap
// `rat_prelude/bernoulli.rs`'s own module doc names as out of reach. Instead
// the whole Bernoulli argument is redone at the `CReal` level, with the
// accumulator kept as `embed (l_term rat q n)` (`l_term`/`one_le_l` above,
// RAT-level, reused verbatim) -- `l_term(q, succ j)` is `ι`-defeq to
// `radd (l_term q j) q` regardless of `j`'s symbolic-ness, and
// `CReal.ofRat_add` relates `embed` of that sum to `add (embed lj) (embed q)`.
// ---------------------------------------------------------------------------

/// `Equiv (embed a) (embed b)`, from `Eq Rat a b` -- congruence of `embed`
/// along a `Rat`-level rewrite.
fn embed_eq_to_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let embed_a = embed(d, p, a);
    let refl = d.lemma(p.equiv_refl, &[embed_a]);
    rat_eq_rewrite(d, a, b, heq, refl, &|d, t| {
        let embed_t = embed(d, p, t);
        equiv(d, p, embed_a, embed_t)
    })
}

/// `le (mul a c) (mul b c)`, from `le (mul c a) (mul c b)` via `mul_comm`
/// twice -- this prelude has `mul_le_mul_of_nonneg_left` only.
fn mul_le_mul_of_nonneg_right(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    hc: ExprId,
    hab: ExprId,
) -> ExprId {
    let raw = d.lemma(p.mul_le_mul_of_nonneg_left, &[c, a, b, hc, hab]);
    let ca = cmul(d, p, c, a);
    let cb = cmul(d, p, c, b);
    let ac = cmul(d, p, a, c);
    let bc = cmul(d, p, b, c);
    let comm_a = d.lemma(p.mul_comm, &[c, a]);
    let comm_b = d.lemma(p.mul_comm, &[c, b]);
    d.lemma(p.le_congr, &[ca, ac, cb, bc, comm_a, comm_b, raw])
}

/// `Equiv (mul one x) x`.
fn creal_one_mul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let one = d.kernel().const_(p.one, vec![]);
    let comm = d.lemma(p.mul_comm, &[one, x]);
    let one_x = cmul(d, p, one, x);
    let x_one = cmul(d, p, x, one);
    let fix = d.lemma(p.mul_one, &[x]);
    d.lemma(p.equiv_trans, &[one_x, x_one, x, comm, fix])
}

/// `Equiv (mul (add a b) c) (add (mul a c) (mul b c))` -- right
/// distributivity, derived from `left_distrib` (the only form this prelude
/// has as a field) via `mul_comm` on all three products.
fn creal_right_distrib(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let ab = cadd(d, p, a, b);
    let ab_c = cmul(d, p, ab, c);
    let c_ab = cmul(d, p, c, ab);
    let comm1 = d.lemma(p.mul_comm, &[ab, c]);
    let ld = d.lemma(p.left_distrib, &[c, a, b]);
    let ca = cmul(d, p, c, a);
    let cb = cmul(d, p, c, b);
    let ac = cmul(d, p, a, c);
    let bc = cmul(d, p, b, c);
    let comm_a = d.lemma(p.mul_comm, &[c, a]);
    let comm_b = d.lemma(p.mul_comm, &[c, b]);
    let congr = d.lemma(p.add_congr, &[ca, ac, cb, bc, comm_a, comm_b]);
    let ca_cb = cadd(d, p, ca, cb);
    let ac_bc = cadd(d, p, ac, bc);
    let s1 = d.lemma(p.equiv_trans, &[ab_c, c_ab, ca_cb, comm1, ld]);
    d.lemma(p.equiv_trans, &[ab_c, ca_cb, ac_bc, s1, congr])
}

/// `Eq Rat (natDivSucc (succ n) n) rone` -- mirrors
/// `rat_pow_half_le_nat_div_succ`'s own `x0` sub-derivation above, generalized
/// to a symbolic `n`: `nat_div_succ_scale(n, 0)` gives `natDivSucc (succ n)
/// ((succ n)*0 + n) = natDivSucc 1 0`, and `(succ n)*0 + n` reduces to `n` via
/// `Nat.mul_zero` + `Nat.zero_add`.
pub(super) fn nat_div_succ_succ_self_eq_one(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    n: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero_nat = d.num(0);
    let succ_n = d.succ(n);
    let raw = d.lemma(rat.nat_div_succ_scale, &[n, zero_nat]);
    let idx1 = NatOps::mul(d, succ_n, zero_nat);
    let mul_zero_name = d.prelude().mul_zero;
    let mul_zero_h = d.lemma(mul_zero_name, &[succ_n]);
    let idx1_plus_n = NatOps::add(d, idx1, n);
    let zero_plus_n = NatOps::add(d, zero_nat, n);
    let lhs = d.const_app(rat.nat_div_succ, &[succ_n, idx1_plus_n]);
    let mid1 = d.const_app(rat.nat_div_succ, &[succ_n, zero_plus_n]);
    let step1 = nat_eq_to_rat(d, idx1, zero_nat, mul_zero_h, &|d, k| {
        let idx = NatOps::add(d, k, n);
        d.const_app(rat.nat_div_succ, &[succ_n, idx])
    });
    let zero_add_name = d.prelude().zero_add;
    let zero_add_h = d.lemma(zero_add_name, &[n]);
    let mid2 = d.const_app(rat.nat_div_succ, &[succ_n, n]);
    let step2 = nat_eq_to_rat(d, zero_plus_n, n, zero_add_h, &|d, k| {
        d.const_app(rat.nat_div_succ, &[succ_n, k])
    });
    let one_nat = d.num(1);
    let unit_rat = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
    let one_r = rone(d, rat);
    let mid1_to_lhs = rsymm(d, lhs, mid1, step1);
    let mid1_to_unit = rtrans(d, mid1, lhs, unit_rat, mid1_to_lhs, raw);
    let mid1_to_one = rtrans(d, mid1, unit_rat, one_r, mid1_to_unit, unit_eq_one);
    let mid2_to_mid1 = rsymm(d, mid1, mid2, step2);
    rtrans(d, mid2, mid1, one_r, mid2_to_mid1, mid1_to_one)
}

/// Given an EXACT `Rat` identity `a*dd = 1` (`h_eq`) and a `CReal` bound
/// `mul (embed a) y ≤ b` (`h_le`, `b` arbitrary), concludes `y ≤ mul (embed
/// dd) b` -- multiplying through by the nonnegative `embed dd` and using
/// `h_eq` (lifted via `of_rat_mul`) to collapse `embed dd * embed a` to
/// `one`. No `CReal.inv`/`PosBound` anywhere.
#[allow(clippy::too_many_arguments)]
fn creal_cancel_exact(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    y: ExprId,
    dd: ExprId,
    b: ExprId,
    h_eq: ExprId,
    h_dd_nonneg: ExprId,
    h_le: ExprId,
) -> ExprId {
    let rat = p.rat;
    let a_emb = embed(d, p, a);
    let dd_emb = embed(d, p, dd);
    let ay = cmul(d, p, a_emb, y);

    let step1 = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[dd_emb, ay, b, h_dd_nonneg, h_le],
    );
    let dd_ay = cmul(d, p, dd_emb, ay);
    let dd_b = cmul(d, p, dd_emb, b);

    let assoc = d.lemma(p.mul_assoc, &[dd_emb, a_emb, y]); // Equiv dd_a_y dd_ay
    let dd_a = cmul(d, p, dd_emb, a_emb);
    let dd_a_y = cmul(d, p, dd_a, y);
    let assoc_symm = d.lemma(p.equiv_symm, &[dd_a_y, dd_ay, assoc]); // Equiv dd_ay dd_a_y

    let one_r = rone(d, rat);
    let da_rat = rmul(d, dd, a);
    let ad_rat = rmul(d, a, dd);
    let comm_da = d.lemma(rat.mul_comm, &[dd, a]);
    let da_to_one = rtrans(d, da_rat, ad_rat, one_r, comm_da, h_eq);
    let of_rat_mul_da = d.lemma(p.of_rat_mul, &[dd, a]); // Equiv dd_a (embed da_rat)
    let dd_a_equiv_one = embed_eq_to_equiv(d, p, da_rat, one_r, da_to_one);
    let one = d.kernel().const_(p.one, vec![]);
    let embed_da_rat = embed(d, p, da_rat);
    let dd_a_eq_one = d.lemma(
        p.equiv_trans,
        &[dd_a, embed_da_rat, one, of_rat_mul_da, dd_a_equiv_one],
    );

    let refl_y = d.lemma(p.equiv_refl, &[y]);
    let dd_a_y_eq = d.lemma(p.mul_congr, &[dd_a, one, y, y, dd_a_eq_one, refl_y]);
    let one_y = cmul(d, p, one, y);
    let one_mul_y = creal_one_mul(d, p, y);
    let dd_a_y_to_y = d.lemma(p.equiv_trans, &[dd_a_y, one_y, y, dd_a_y_eq, one_mul_y]);

    let dd_ay_to_y = d.lemma(p.equiv_trans, &[dd_ay, dd_a_y, y, assoc_symm, dd_a_y_to_y]);
    let refl_dd_b = d.lemma(p.equiv_refl, &[dd_b]);
    d.lemma(
        p.le_congr,
        &[dd_ay, y, dd_b, dd_b, dd_ay_to_y, refl_dd_b, step1],
    )
}

/// `CReal`-level mirror of `rat_prelude/bernoulli.rs::declare_bernoulli_harmonic_bound`'s
/// proof, with the `Rat` carrier `x`/`t` replaced by `x : CReal` and `t :=
/// embed q` for a fixed `q : Rat`, and the accumulator kept as `embed (l_term
/// rat q n)` rather than a fresh `CReal`-level `Nat.rec`. Returns a proof of
/// `le (mul (embed (l_term rat q n)) (pow x n)) one`, given `hx0 : le zero x`,
/// `ht : le zero (embed q)` and `hxt : le (mul x (add one (embed q))) one`.
#[allow(clippy::too_many_arguments)]
fn creal_bernoulli_harmonic(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    q: ExprId,
    hx0: ExprId,
    ht: ExprId,
    hxt: ExprId,
    n: ExprId,
) -> ExprId {
    let rat = p.rat;
    let one = d.kernel().const_(p.one, vec![]);
    let q_emb = embed(d, p, q);
    let one_plus_t = cadd(d, p, one, q_emb);
    let x_one_plus_t = cmul(d, p, x, one_plus_t);

    // h_xt : le (add x (mul q_emb x)) one, from hxt : le (mul x (add one
    // q_emb)) one, expanded via left_distrib/mul_one/mul_comm.
    let h_xt = {
        let dist = d.lemma(p.left_distrib, &[x, one, q_emb]); // Equiv x_one_plus_t (add x_one x_t)
        let x_one = cmul(d, p, x, one);
        let x_t = cmul(d, p, x, q_emb);
        let fix1 = d.lemma(p.mul_one, &[x]); // Equiv x_one x
        let refl_xt = d.lemma(p.equiv_refl, &[x_t]);
        let congr1 = d.lemma(p.add_congr, &[x_one, x, x_t, x_t, fix1, refl_xt]);
        let x_one_plus_xt = cadd(d, p, x_one, x_t);
        let x_plus_xt = cadd(d, p, x, x_t);
        let step1 = d.lemma(
            p.equiv_trans,
            &[x_one_plus_t, x_one_plus_xt, x_plus_xt, dist, congr1],
        );
        let fix2 = d.lemma(p.mul_comm, &[x, q_emb]); // Equiv x_t t_x
        let t_x = cmul(d, p, q_emb, x);
        let refl_x = d.lemma(p.equiv_refl, &[x]);
        let congr2 = d.lemma(p.add_congr, &[x, x, x_t, t_x, refl_x, fix2]);
        let x_plus_tx = cadd(d, p, x, t_x);
        let step2 = d.lemma(
            p.equiv_trans,
            &[x_one_plus_t, x_plus_xt, x_plus_tx, step1, congr2],
        );
        let refl_one = d.lemma(p.equiv_refl, &[one]);
        d.lemma(
            p.le_congr,
            &[x_one_plus_t, x_plus_tx, one, one, step2, refl_one, hxt],
        )
    };

    // hx1 : le x one, from x = x*1 ≤ x*(1+t) ≤ 1.
    let hx1 = {
        let zero_c = czero(d, p);
        let one_le_one = d.lemma(p.le_refl, &[one]);
        let sum_le = d.lemma(p.add_le_add, &[one, one, zero_c, q_emb, one_le_one, ht]);
        let one_plus_zero = cadd(d, p, one, zero_c);
        let add_zero_eq = d.lemma(p.add_zero, &[one]);
        let refl_opt = d.lemma(p.equiv_refl, &[one_plus_t]);
        let one_le_one_plus_t = d.lemma(
            p.le_congr,
            &[
                one_plus_zero,
                one,
                one_plus_t,
                one_plus_t,
                add_zero_eq,
                refl_opt,
                sum_le,
            ],
        );
        let raw = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[x, one, one_plus_t, hx0, one_le_one_plus_t],
        );
        let x_one2 = cmul(d, p, x, one);
        let fix = d.lemma(p.mul_one, &[x]);
        let refl_xopt = d.lemma(p.equiv_refl, &[x_one_plus_t]);
        let step_a = d.lemma(
            p.le_congr,
            &[x_one2, x, x_one_plus_t, x_one_plus_t, fix, refl_xopt, raw],
        );
        d.lemma(p.le_trans, &[x, x_one_plus_t, one, step_a, hxt])
    };

    let motive = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
        let ly = l_term(d, rat, q, y);
        let ly_emb = embed(d, p, ly);
        let py = d.const_app(p.pow, &[x, y]);
        let prod = cmul(d, p, ly_emb, py);
        let one_l = d.kernel().const_(p.one, vec![]);
        cle(d, p, prod, one_l)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let one_one = cmul(d, p, one, one);
        let mul_one_eq = d.lemma(p.mul_one, &[one]); // Equiv one_one one
        let sym = d.lemma(p.equiv_symm, &[one_one, one, mul_one_eq]); // Equiv one one_one
        let base_at_one = d.lemma(p.le_refl, &[one]);
        let refl_one2 = d.lemma(p.equiv_refl, &[one]);
        d.lemma(
            p.le_congr,
            &[one, one_one, one, one, sym, refl_one2, base_at_one],
        )
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let lj_rat = l_term(d, rat, q, j);
        let lj = embed(d, p, lj_rat);
        let pj = d.const_app(p.pow, &[x, j]);

        let pow_le_one_j = d.lemma(p.pow_le_one, &[x, hx0, hx1, j]);
        let raw_hpx = mul_le_mul_of_nonneg_right(d, p, pj, one, x, hx0, pow_le_one_j);
        let one_x = cmul(d, p, one, x);
        let one_mul_x = creal_one_mul(d, p, x);
        let pjx = cmul(d, p, pj, x);
        let refl_pjx = d.lemma(p.equiv_refl, &[pjx]);
        let hpx = d.lemma(
            p.le_congr,
            &[pjx, pjx, one_x, x, refl_pjx, one_mul_x, raw_hpx],
        );

        let lj_pj = cmul(d, p, lj, pj);
        let assoc = d.lemma(p.mul_assoc, &[lj, pj, x]); // Equiv lj_pj_x lj_pjx
        let raw_term1 = mul_le_mul_of_nonneg_right(d, p, lj_pj, one, x, hx0, ih);
        let lj_pj_x = cmul(d, p, lj_pj, x);
        let lj_pjx = cmul(d, p, lj, pjx);
        let refl_one_x = d.lemma(p.equiv_refl, &[one_x]);
        let step_assoc = d.lemma(
            p.le_congr,
            &[lj_pj_x, lj_pjx, one_x, one_x, assoc, refl_one_x, raw_term1],
        );
        let refl_lj_pjx = d.lemma(p.equiv_refl, &[lj_pjx]);
        let term1 = d.lemma(
            p.le_congr,
            &[lj_pjx, lj_pjx, one_x, x, refl_lj_pjx, one_mul_x, step_assoc],
        );

        let t_pjx = cmul(d, p, q_emb, pjx);
        let t_x = cmul(d, p, q_emb, x);
        let term2 = d.lemma(p.mul_le_mul_of_nonneg_left, &[q_emb, pjx, x, ht, hpx]);

        let sum_bound = d.lemma(p.add_le_add, &[lj_pjx, x, t_pjx, t_x, term1, term2]);
        let lhs_sum = cadd(d, p, lj_pjx, t_pjx);
        let rhs_sum = cadd(d, p, x, t_x);
        let final_le = d.lemma(p.le_trans, &[lhs_sum, rhs_sum, one, sum_bound, h_xt]);

        let rd = creal_right_distrib(d, p, lj, q_emb, pjx);
        let lj_plus_t = cadd(d, p, lj, q_emb);
        let target_lhs = cmul(d, p, lj_plus_t, pjx);
        let rd_sym = d.lemma(p.equiv_symm, &[target_lhs, lhs_sum, rd]);
        let refl_one_b = d.lemma(p.equiv_refl, &[one]);
        let step_final = d.lemma(
            p.le_congr,
            &[lhs_sum, target_lhs, one, one, rd_sym, refl_one_b, final_le],
        );

        let add_eq = d.lemma(p.of_rat_add, &[lj_rat, q]); // Equiv lj_plus_t (embed (radd lj_rat q))
        let l_succ_rat = radd(d, lj_rat, q);
        let l_succ = embed(d, p, l_succ_rat);
        let refl_pjx2 = d.lemma(p.equiv_refl, &[pjx]);
        let l_succ_pjx = cmul(d, p, l_succ, pjx);
        let mul_congr_ls = d.lemma(
            p.mul_congr,
            &[lj_plus_t, l_succ, pjx, pjx, add_eq, refl_pjx2],
        );
        // mul_congr_ls : Equiv target_lhs l_succ_pjx
        let refl_one_c4 = d.lemma(p.equiv_refl, &[one]);
        d.lemma(
            p.le_congr,
            &[
                target_lhs,
                l_succ_pjx,
                one,
                one,
                mul_congr_ls,
                refl_one_c4,
                step_final,
            ],
        )
    };

    d.induct(&motive, &base, &step, n)
}

/// By induction on `m`: `le (embed (natDivSucc (succ m) 0)) (mul (embed
/// k_rat) (embed (l_term rat q m)))`, given `h_k_ge_one : le one (embed
/// k_rat)` and `h_kq : le one (mul (embed k_rat) (embed q))`.
fn k_relation_creal(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    q: ExprId,
    k_rat: ExprId,
    h_k_ge_one: ExprId,
    h_kq: ExprId,
    m: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero_nat = d.num(0);
    let one_c = d.kernel().const_(p.one, vec![]);
    let k_emb = embed(d, p, k_rat);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let succ_x = d.succ(x);
        let lhs_rat = d.const_app(rat.nat_div_succ, &[succ_x, zero_nat]);
        let lhs = embed(d, p, lhs_rat);
        let lx_rat = l_term(d, rat, q, x);
        let lx = embed(d, p, lx_rat);
        let rhs = cmul(d, p, k_emb, lx);
        cle(d, p, lhs, rhs)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let one_nat = d.num(1);
        let unit_rat = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
        let one_r = rone(d, rat);
        let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
        let unit_equiv_one = embed_eq_to_equiv(d, p, unit_rat, one_r, unit_eq_one);
        let unit_emb = embed(d, p, unit_rat);
        let hxx = d.lemma(p.equiv_symm, &[unit_emb, one_c, unit_equiv_one]);
        let mul_one_k = d.lemma(p.mul_one, &[k_emb]);
        let k_one = cmul(d, p, k_emb, one_c);
        let hyy = d.lemma(p.equiv_symm, &[k_one, k_emb, mul_one_k]);
        d.lemma(
            p.le_congr,
            &[one_c, unit_emb, k_emb, k_one, hxx, hyy, h_k_ge_one],
        )
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let succ_j = d.succ(j);
        let a_j_rat = d.const_app(rat.nat_div_succ, &[succ_j, zero_nat]);
        let a_j = embed(d, p, a_j_rat);
        let lj_rat = l_term(d, rat, q, j);
        let lj = embed(d, p, lj_rat);
        let q_emb = embed(d, p, q);

        let k_lj = cmul(d, p, k_emb, lj);
        let k_q = cmul(d, p, k_emb, q_emb);
        let combined = d.lemma(p.add_le_add, &[a_j, k_lj, one_c, k_q, ih, h_kq]);

        let lj_plus_q = cadd(d, p, lj, q_emb);
        let k_lj_plus_q = cmul(d, p, k_emb, lj_plus_q);
        let k_lj_plus_k_q = cadd(d, p, k_lj, k_q);
        let rhs_dist = d.lemma(p.left_distrib, &[k_emb, lj, q_emb]); // Equiv k_lj_plus_q k_lj_plus_k_q
        let rhs_eq = d.lemma(p.equiv_symm, &[k_lj_plus_q, k_lj_plus_k_q, rhs_dist]);

        // lhs_eq : Equiv (add a_j one_c) a_succ_j
        let succ_succ_j = d.succ(succ_j);
        let a_succ_j_rat = d.const_app(rat.nat_div_succ, &[succ_succ_j, zero_nat]);
        let one_nat = d.num(1);
        let unit_rat = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
        let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
        let sum_add = d.lemma(rat.nat_div_succ_add, &[succ_j, one_nat, zero_nat]);
        let sum_unit = radd(d, a_j_rat, unit_rat);
        let one_r = rone(d, rat);
        let sum_one = radd(d, a_j_rat, one_r);
        let unit_to_one = rcongr(d, unit_rat, one_r, unit_eq_one, &|d, t| radd(d, a_j_rat, t));
        let sum_one_to_unit = rsymm(d, sum_unit, sum_one, unit_to_one);
        let sum_one_to_a_succ_j =
            rtrans(d, sum_one, sum_unit, a_succ_j_rat, sum_one_to_unit, sum_add);
        let lhs_equiv_a = embed_eq_to_equiv(d, p, sum_one, a_succ_j_rat, sum_one_to_a_succ_j);
        let embed_sum = embed(d, p, sum_one);
        let add_eq = d.lemma(p.of_rat_add, &[a_j_rat, one_r]); // Equiv (add a_j one_c) embed_sum
        let a_plus_one = cadd(d, p, a_j, one_c);
        let a_succ_j = embed(d, p, a_succ_j_rat);
        let lhs_eq = d.lemma(
            p.equiv_trans,
            &[a_plus_one, embed_sum, a_succ_j, add_eq, lhs_equiv_a],
        );

        let via_congr = d.lemma(
            p.le_congr,
            &[
                a_plus_one,
                a_succ_j,
                k_lj_plus_k_q,
                k_lj_plus_q,
                lhs_eq,
                rhs_eq,
                combined,
            ],
        );

        let add_lj_q_eq = d.lemma(p.of_rat_add, &[lj_rat, q]); // Equiv lj_plus_q (embed (radd lj_rat q))
        let l_succ_j_rat = radd(d, lj_rat, q);
        let l_succ_j = embed(d, p, l_succ_j_rat);
        let target_rhs = cmul(d, p, k_emb, l_succ_j);
        let refl_a_succ_j = d.lemma(p.equiv_refl, &[a_succ_j]);
        let refl_k = d.lemma(p.equiv_refl, &[k_emb]);
        let mul_congr_rhs = d.lemma(
            p.mul_congr,
            &[k_emb, k_emb, lj_plus_q, l_succ_j, refl_k, add_lj_q_eq],
        );
        d.lemma(
            p.le_congr,
            &[
                a_succ_j,
                a_succ_j,
                k_lj_plus_q,
                target_rhs,
                refl_a_succ_j,
                mul_congr_rhs,
                via_congr,
            ],
        )
    };

    d.induct(&motive, &base, &step, m)
}

/// The shared, non-existential leaf of `CReal.pow_le_natDivSucc_of_lt` and
/// `CReal.pow_le_natDivSucc_of_gap`: a proof of
/// `le (pow x m) (ofRat (natDivSucc (Nat.succ k3) m))`, given the rational
/// gap `q` (`x + q ≤ 1`) and a `PosBound (ofRat q) k3` modulus as DATA.
///
/// This is the whole of what [`declare_pow_le_nat_div_succ_of_lt`] used to
/// build inline underneath its two `Exists` eliminations. Nothing in the
/// argument needs an existential -- the two witnesses it consumes are `q` and
/// `k3`, and that theorem obtains them from `lt x one` and
/// [`super::CRealPrelude::pos_bound_of_lt`] only because its own statement
/// quantifies over an arbitrary `x`. A caller holding a CONCRETE ratio can
/// write both down, which is what [`declare_pow_le_nat_div_succ_of_gap`]
/// exposes.
///
/// `ht : le zero (ofRat q)` is derived here from `h_pb` rather than taken as
/// a parameter (`0 ≤ 1/(k3+1) ≤ q`), so the `Rat.lt Rat.zero q` hypothesis
/// the `_of_lt` route carries is not needed at all.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn pow_le_nat_div_succ_gap_leaf(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    hx0: ExprId,
    q: ExprId,
    hle: ExprId,
    k3: ExprId,
    h_pb: ExprId,
    m: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero_nat = d.num(0);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);
    let q_emb = embed(d, p, q);

    // ht : le zero_c q_emb -- `0 ≤ 1/(k3+1) ≤ q`, the second step being
    // `h_pb` itself (`CReal.PosBound y k` unfolds to `le (ofRat (natDivSucc 1
    // k)) y`, the same defeq `h_kq` below already relies on).
    let ht = {
        let one_nat = d.num(1);
        let small_rat = d.const_app(rat.nat_div_succ, &[one_nat, k3]);
        let small_nonneg_rat = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, k3]);
        let zero_r = rzero(d, rat);
        let small_emb = embed(d, p, small_rat);
        let small_nonneg = d.lemma(p.of_rat_le, &[zero_r, small_rat, small_nonneg_rat]);
        d.lemma(p.le_trans, &[zero_c, small_emb, q_emb, small_nonneg, h_pb])
    };

    let big_k = d.succ(k3);
    let k_rat = d.const_app(rat.nat_div_succ, &[big_k, zero_nat]);
    let k_emb = embed(d, p, k_rat);

    // h_k_ge_one : le one_c k_emb
    let h_k_ge_one = {
        let one_nat = d.num(1);
        let k3_rat = d.const_app(rat.nat_div_succ, &[k3, zero_nat]);
        let unit_rat = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
        let sum_add = d.lemma(rat.nat_div_succ_add, &[k3, one_nat, zero_nat]);
        let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
        let one_r = rone(d, rat);
        let sum_unit = radd(d, k3_rat, unit_rat);
        let sum_one = radd(d, k3_rat, one_r);
        let unit_to_one = rcongr(d, unit_rat, one_r, unit_eq_one, &|d, t| radd(d, k3_rat, t));
        let sum_one_to_unit = rsymm(d, sum_unit, sum_one, unit_to_one);
        let sum_one_to_k = rtrans(d, sum_one, sum_unit, k_rat, sum_one_to_unit, sum_add);
        let k3_rat_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[k3, zero_nat]);
        let refl_one_r = d.lemma(rat.le_refl, &[one_r]);
        let zero_r3 = rzero(d, rat);
        let sum_le = d.lemma(
            rat.add_le_add,
            &[zero_r3, k3_rat, one_r, one_r, k3_rat_nonneg, refl_one_r],
        );
        let zero_plus_one = radd(d, zero_r3, one_r);
        let zero_add_eq = d.lemma(rat.zero_add, &[one_r]);
        let sum_le_at_one =
            rat_eq_rewrite(d, zero_plus_one, one_r, zero_add_eq, sum_le, &|d, t| {
                rle(d, rat, t, sum_one)
            });
        let rone_le_k_rat =
            rat_eq_rewrite(d, sum_one, k_rat, sum_one_to_k, sum_le_at_one, &|d, t| {
                rle(d, rat, one_r, t)
            });
        d.lemma(p.of_rat_le, &[one_r, k_rat, rone_le_k_rat])
    };

    // h_kq : le one_c (mul k_emb q_emb)
    let h_kq = {
        let one_nat2 = d.num(1);
        let small_rat = d.const_app(rat.nat_div_succ, &[one_nat2, k3]);
        let small_emb = embed(d, p, small_rat);
        let zero_r4 = rzero(d, rat);
        let k_rat_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[big_k, zero_nat]);
        let k_emb_nonneg = d.lemma(p.of_rat_le, &[zero_r4, k_rat, k_rat_nonneg]);
        let step1 = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[k_emb, small_emb, q_emb, k_emb_nonneg, h_pb],
        );
        let k_small = cmul(d, p, k_emb, small_emb);
        let k_q = cmul(d, p, k_emb, q_emb);

        let of_rat_mul_ks = d.lemma(p.of_rat_mul, &[k_rat, small_rat]);
        let prod_rat = rmul(d, k_rat, small_rat);
        let scale_eq = d.lemma(rat.nat_div_succ_mul, &[big_k, one_nat2, k3]);
        let big_k_mul_one = NatOps::mul(d, big_k, one_nat2);
        let mid_rat = d.const_app(rat.nat_div_succ, &[big_k_mul_one, k3]);
        let mid2_rat = d.const_app(rat.nat_div_succ, &[big_k, k3]);
        let mul_one_nat_name = d.prelude().mul_one;
        let mul_one_nat_h = d.lemma(mul_one_nat_name, &[big_k]);
        let idx_step = nat_eq_to_rat(d, big_k_mul_one, big_k, mul_one_nat_h, &|d, kk| {
            d.const_app(rat.nat_div_succ, &[kk, k3])
        });
        let x0 = nat_div_succ_succ_self_eq_one(d, p, k3);
        let prod_to_mid2 = rtrans(d, prod_rat, mid_rat, mid2_rat, scale_eq, idx_step);
        let one_r2 = rone(d, rat);
        let prod_to_one = rtrans(d, prod_rat, mid2_rat, one_r2, prod_to_mid2, x0);
        let prod_equiv_one = embed_eq_to_equiv(d, p, prod_rat, one_r2, prod_to_one);
        let embed_prod = embed(d, p, prod_rat);
        let k_small_eq_one = d.lemma(
            p.equiv_trans,
            &[k_small, embed_prod, one_c, of_rat_mul_ks, prod_equiv_one],
        );

        let refl_kq = d.lemma(p.equiv_refl, &[k_q]);
        d.lemma(
            p.le_congr,
            &[k_small, one_c, k_q, k_q, k_small_eq_one, refl_kq, step1],
        )
    };

    // ---- hxt : le (mul x (add one_c q_emb)) one_c ----
    let hxt = {
        let neg_q_emb = cneg(d, p, q_emb);
        let refl_neg_q = d.lemma(p.le_refl, &[neg_q_emb]);
        let x_plus_q = cadd(d, p, x, q_emb);
        let shifted = d.lemma(
            p.add_le_add,
            &[x_plus_q, one_c, neg_q_emb, neg_q_emb, hle, refl_neg_q],
        );
        let lhs_shifted = cadd(d, p, x_plus_q, neg_q_emb);
        let assoc = d.lemma(p.add_assoc, &[x, q_emb, neg_q_emb]);
        let q_plus_negq = cadd(d, p, q_emb, neg_q_emb);
        let add_neg_h = d.lemma(p.add_neg, &[q_emb]);
        let refl_x = d.lemma(p.equiv_refl, &[x]);
        let congr_xz = d.lemma(p.add_congr, &[x, x, q_plus_negq, zero_c, refl_x, add_neg_h]);
        let x_plus_qnq = cadd(d, p, x, q_plus_negq);
        let x_plus_zero = cadd(d, p, x, zero_c);
        let step_xz = d.lemma(
            p.equiv_trans,
            &[lhs_shifted, x_plus_qnq, x_plus_zero, assoc, congr_xz],
        );
        let add_zero_x = d.lemma(p.add_zero, &[x]);
        let lhs_to_x = d.lemma(
            p.equiv_trans,
            &[lhs_shifted, x_plus_zero, x, step_xz, add_zero_x],
        );
        let one_minus_q = cadd(d, p, one_c, neg_q_emb);
        let refl_omq = d.lemma(p.equiv_refl, &[one_minus_q]);
        let hr_le = d.lemma(
            p.le_congr,
            &[
                lhs_shifted,
                x,
                one_minus_q,
                one_minus_q,
                lhs_to_x,
                refl_omq,
                shifted,
            ],
        );

        // hx_le_one : le x one_c   (x ≤ 1-q ≤ 1)
        let hx_le_one = {
            let neg_zero_c = cneg(d, p, zero_c);
            let h1 = d.lemma(p.neg_le_neg, &[zero_c, q_emb, ht]);
            let an = d.lemma(p.add_neg, &[zero_c]);
            let az = d.lemma(p.add_zero, &[neg_zero_c]);
            let zero_plus_negzero = cadd(d, p, zero_c, neg_zero_c);
            let negzero_plus_zero = cadd(d, p, neg_zero_c, zero_c);
            let comm0 = d.lemma(p.add_comm, &[zero_c, neg_zero_c]);
            let e1 = d.lemma(
                p.equiv_trans,
                &[zero_plus_negzero, negzero_plus_zero, neg_zero_c, comm0, az],
            );
            let e1_symm = d.lemma(p.equiv_symm, &[zero_plus_negzero, neg_zero_c, e1]);
            let neg_zero_eq_zero = d.lemma(
                p.equiv_trans,
                &[neg_zero_c, zero_plus_negzero, zero_c, e1_symm, an],
            );
            let refl_negq = d.lemma(p.equiv_refl, &[neg_q_emb]);
            let neg_q_nonpos = d.lemma(
                p.le_congr,
                &[
                    neg_q_emb,
                    neg_q_emb,
                    neg_zero_c,
                    zero_c,
                    refl_negq,
                    neg_zero_eq_zero,
                    h1,
                ],
            );
            let refl_one_c = d.lemma(p.le_refl, &[one_c]);
            let one_plus_zero2 = cadd(d, p, one_c, zero_c);
            let sum_le3 = d.lemma(
                p.add_le_add,
                &[one_c, one_c, neg_q_emb, zero_c, refl_one_c, neg_q_nonpos],
            );
            let add_zero_one = d.lemma(p.add_zero, &[one_c]);
            let refl_omq2 = d.lemma(p.equiv_refl, &[one_minus_q]);
            let omq_le_one = d.lemma(
                p.le_congr,
                &[
                    one_minus_q,
                    one_minus_q,
                    one_plus_zero2,
                    one_c,
                    refl_omq2,
                    add_zero_one,
                    sum_le3,
                ],
            );
            d.lemma(p.le_trans, &[x, one_minus_q, one_c, hr_le, omq_le_one])
        };

        // xq_le_q : le (mul x q_emb) q_emb
        let xq = cmul(d, p, x, q_emb);
        let xq_le_q = {
            let raw = mul_le_mul_of_nonneg_right(d, p, x, one_c, q_emb, ht, hx_le_one);
            let one_q = cmul(d, p, one_c, q_emb);
            let one_mul_q = creal_one_mul(d, p, q_emb);
            let refl_xq = d.lemma(p.equiv_refl, &[xq]);
            d.lemma(p.le_congr, &[xq, xq, one_q, q_emb, refl_xq, one_mul_q, raw])
        };

        // omq_plus_q_eq_one : Equiv (add one_minus_q q_emb) one_c
        let omq_plus_q = cadd(d, p, one_minus_q, q_emb);
        let assoc2 = d.lemma(p.add_assoc, &[one_c, neg_q_emb, q_emb]);
        let nq_plus_q = cadd(d, p, neg_q_emb, q_emb);
        let q_plus_nq = cadd(d, p, q_emb, neg_q_emb);
        let comm_nq = d.lemma(p.add_comm, &[neg_q_emb, q_emb]);
        let refl_one_c2 = d.lemma(p.equiv_refl, &[one_c]);
        let congr_nq = d.lemma(
            p.add_congr,
            &[one_c, one_c, nq_plus_q, q_plus_nq, refl_one_c2, comm_nq],
        );
        let addneg_q = d.lemma(p.add_neg, &[q_emb]);
        let congr_zero = d.lemma(
            p.add_congr,
            &[one_c, one_c, q_plus_nq, zero_c, refl_one_c2, addneg_q],
        );
        let one_plus_zero3 = cadd(d, p, one_c, zero_c);
        let add_zero_one2 = d.lemma(p.add_zero, &[one_c]);
        let one_plus_nq_plus_q = cadd(d, p, one_c, nq_plus_q);
        let one_plus_q_plus_nq = cadd(d, p, one_c, q_plus_nq);
        let step_a2 = d.lemma(
            p.equiv_trans,
            &[
                omq_plus_q,
                one_plus_nq_plus_q,
                one_plus_q_plus_nq,
                assoc2,
                congr_nq,
            ],
        );
        let step_b2 = d.lemma(
            p.equiv_trans,
            &[
                omq_plus_q,
                one_plus_q_plus_nq,
                one_plus_zero3,
                step_a2,
                congr_zero,
            ],
        );
        let omq_plus_q_eq_one = d.lemma(
            p.equiv_trans,
            &[omq_plus_q, one_plus_zero3, one_c, step_b2, add_zero_one2],
        );

        // final_bound : le (add one_minus_q xq) one_c
        let sum4lhs = cadd(d, p, one_minus_q, xq);
        let refl_omq3 = d.lemma(p.le_refl, &[one_minus_q]);
        let sum_le4 = d.lemma(
            p.add_le_add,
            &[one_minus_q, one_minus_q, xq, q_emb, refl_omq3, xq_le_q],
        );
        let refl_sum4lhs = d.lemma(p.equiv_refl, &[sum4lhs]);
        let final_bound = d.lemma(
            p.le_congr,
            &[
                sum4lhs,
                sum4lhs,
                omq_plus_q,
                one_c,
                refl_sum4lhs,
                omq_plus_q_eq_one,
                sum_le4,
            ],
        );

        // x_one_plus_t ~ (add x xq) ≤ (add one_minus_q xq) ≤ one_c
        let one_plus_t_outer = cadd(d, p, one_c, q_emb);
        let x_one_plus_t = cmul(d, p, x, one_plus_t_outer);
        let x_one_c = cmul(d, p, x, one_c);
        let dist = d.lemma(p.left_distrib, &[x, one_c, q_emb]);
        let mul_one_x = d.lemma(p.mul_one, &[x]);
        let refl_xq2 = d.lemma(p.equiv_refl, &[xq]);
        let congr_x = d.lemma(p.add_congr, &[x_one_c, x, xq, xq, mul_one_x, refl_xq2]);
        let x_plus_xq = cadd(d, p, x, xq);
        let x_one_c_plus_xq = cadd(d, p, x_one_c, xq);
        let dist2 = d.lemma(
            p.equiv_trans,
            &[x_one_plus_t, x_one_c_plus_xq, x_plus_xq, dist, congr_x],
        );

        let le_refl_xq = d.lemma(p.le_refl, &[xq]);
        let bound1 = d.lemma(p.add_le_add, &[x, one_minus_q, xq, xq, hr_le, le_refl_xq]);
        let chain1 = d.lemma(
            p.le_trans,
            &[x_plus_xq, sum4lhs, one_c, bound1, final_bound],
        );
        let refl_one_c3 = d.lemma(p.equiv_refl, &[one_c]);
        let dist2_symm = d.lemma(p.equiv_symm, &[x_one_plus_t, x_plus_xq, dist2]);
        d.lemma(
            p.le_congr,
            &[
                x_plus_xq,
                x_one_plus_t,
                one_c,
                one_c,
                dist2_symm,
                refl_one_c3,
                chain1,
            ],
        )
    };

    // ---- per-m decay bound, then Exists.intro over K := K1*K1 ----

    let l_bound_m = creal_bernoulli_harmonic(d, p, x, q, hx0, ht, hxt, m);
    let kr_m = k_relation_creal(d, p, q, k_rat, h_k_ge_one, h_kq, m);

    // Step A: kr_m * pow(x,m) (nonneg, right) -> le (mul (embed a_m) (pow x m)) k_emb
    let succ_m = d.succ(m);
    let a_m_rat = d.const_app(rat.nat_div_succ, &[succ_m, zero_nat]);
    let a_m = embed(d, p, a_m_rat);
    let pow_xm = d.const_app(p.pow, &[x, m]);
    let pow_nonneg_m = d.lemma(p.pow_nonneg, &[x, hx0, m]);
    let lm_rat = l_term(d, rat, q, m);
    let lm = embed(d, p, lm_rat);
    let k_lm = cmul(d, p, k_emb, lm);
    let step_ar = mul_le_mul_of_nonneg_right(d, p, a_m, k_lm, pow_xm, pow_nonneg_m, kr_m);
    // step_ar : le (mul a_m pow_xm) (mul k_lm pow_xm)
    let a_m_pow = cmul(d, p, a_m, pow_xm);
    let k_lm_pow = cmul(d, p, k_lm, pow_xm);

    let assoc3 = d.lemma(p.mul_assoc, &[k_emb, lm, pow_xm]); // Equiv k_lm_pow (mul k_emb (mul lm pow_xm))
    let lm_pow = cmul(d, p, lm, pow_xm);
    let k_lm_pow2 = cmul(d, p, k_emb, lm_pow);
    let k_rat_nonneg2 = d.lemma(rat.zero_le_nat_div_succ, &[big_k, zero_nat]);
    let zero_r5 = rzero(d, rat);
    let k_emb_nonneg2 = d.lemma(p.of_rat_le, &[zero_r5, k_rat, k_rat_nonneg2]);
    let step_scale = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[k_emb, lm_pow, one_c, k_emb_nonneg2, l_bound_m],
    );
    // step_scale : le k_lm_pow2 (mul k_emb one_c)
    let k_one2 = cmul(d, p, k_emb, one_c);
    let mul_one_k2 = d.lemma(p.mul_one, &[k_emb]);
    let refl_k_lm_pow2 = d.lemma(p.equiv_refl, &[k_lm_pow2]);
    let step_scale2 = d.lemma(
        p.le_congr,
        &[
            k_lm_pow2,
            k_lm_pow2,
            k_one2,
            k_emb,
            refl_k_lm_pow2,
            mul_one_k2,
            step_scale,
        ],
    );
    // step_scale2 : le k_lm_pow2 k_emb

    let refl_k_emb = d.lemma(p.equiv_refl, &[k_emb]);
    let assoc3_symm = d.lemma(p.equiv_symm, &[k_lm_pow, k_lm_pow2, assoc3]);
    let step_bridge = d.lemma(
        p.le_congr,
        &[
            k_lm_pow2,
            k_lm_pow,
            k_emb,
            k_emb,
            assoc3_symm,
            refl_k_emb,
            step_scale2,
        ],
    );
    // step_bridge : le k_lm_pow k_emb

    let ay_le_k = d.lemma(
        p.le_trans,
        &[a_m_pow, k_lm_pow, k_emb, step_ar, step_bridge],
    );
    // ay_le_k : le (mul a_m pow_xm) k_emb

    // Step B: exact cancellation via natDivSucc(1,m) as a_m's exact reciprocal.
    let one_nat3 = d.num(1);
    let dd_rat = d.const_app(rat.nat_div_succ, &[one_nat3, m]);
    let ad_dd_eq_one = {
        // a_m_rat * dd_rat = 1, via nat_div_succ_mul + mul_one + the x0-style identity.
        let prod2 = rmul(d, a_m_rat, dd_rat);
        let scale_eq2 = d.lemma(rat.nat_div_succ_mul, &[succ_m, one_nat3, m]);
        let succ_m_mul_one = NatOps::mul(d, succ_m, one_nat3);
        let mid_rat2 = d.const_app(rat.nat_div_succ, &[succ_m_mul_one, m]);
        let mid2_rat2 = d.const_app(rat.nat_div_succ, &[succ_m, m]);
        let mul_one_nat_name2 = d.prelude().mul_one;
        let mul_one_h2 = d.lemma(mul_one_nat_name2, &[succ_m]);
        let idx_step2 = nat_eq_to_rat(d, succ_m_mul_one, succ_m, mul_one_h2, &|d, kk| {
            d.const_app(rat.nat_div_succ, &[kk, m])
        });
        let x0b = nat_div_succ_succ_self_eq_one(d, p, m);
        let prod_to_mid2b = rtrans(d, prod2, mid_rat2, mid2_rat2, scale_eq2, idx_step2);
        let one_r3 = rone(d, rat);
        rtrans(d, prod2, mid2_rat2, one_r3, prod_to_mid2b, x0b)
    };
    let dd_nonneg = {
        let dd_nat_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat3, m]);
        let zero_r6 = rzero(d, rat);
        d.lemma(p.of_rat_le, &[zero_r6, dd_rat, dd_nat_nonneg])
    };
    let pow_le_kdd = creal_cancel_exact(
        d,
        p,
        a_m_rat,
        pow_xm,
        dd_rat,
        k_emb,
        ad_dd_eq_one,
        dd_nonneg,
        ay_le_k,
    );
    // pow_le_kdd : le pow_xm (mul (embed dd_rat) k_emb)

    // Final: embed dd_rat * k_emb ~ embed (natDivSucc (big_k*big_k) m)  [wait: need natDivSucc combining dd (1,m) and k_rat (big_k,0)]
    let final_rat = rmul(d, dd_rat, k_rat);
    let final_of_rat = d.lemma(p.of_rat_mul, &[dd_rat, k_rat]);
    // final_of_rat : Equiv (mul (embed dd_rat) k_emb) (embed final_rat)
    let scale_eq3 = d.lemma(rat.nat_div_succ_mul, &[big_k, one_nat3, m]);
    // scale_eq3 : Eq (rmul k_rat dd_rat) (natDivSucc (big_k*one_nat3) m)   -- note order k_rat*dd_rat
    let big_k_mul_one2 = NatOps::mul(d, big_k, one_nat3);
    let mid_rat3 = d.const_app(rat.nat_div_succ, &[big_k_mul_one2, m]);
    let mid2_rat3 = d.const_app(rat.nat_div_succ, &[big_k, m]);
    let mul_one_nat_name3 = d.prelude().mul_one;
    let mul_one_h3 = d.lemma(mul_one_nat_name3, &[big_k]);
    let idx_step3 = nat_eq_to_rat(d, big_k_mul_one2, big_k, mul_one_h3, &|d, kk| {
        d.const_app(rat.nat_div_succ, &[kk, m])
    });
    let kdd_rat = rmul(d, k_rat, dd_rat);
    let comm_dk = d.lemma(rat.mul_comm, &[dd_rat, k_rat]); // Eq final_rat kdd_rat
    let kdd_to_mid = rtrans(d, kdd_rat, mid_rat3, mid2_rat3, scale_eq3, idx_step3);
    let final_to_kdd = comm_dk;
    let final_to_mid2 = rtrans(d, final_rat, kdd_rat, mid2_rat3, final_to_kdd, kdd_to_mid);
    // final_to_mid2 : Eq final_rat (natDivSucc big_k m)
    let final_equiv = embed_eq_to_equiv(d, p, final_rat, mid2_rat3, final_to_mid2);
    let dd_rat_emb = embed(d, p, dd_rat);
    let dd_k = cmul(d, p, dd_rat_emb, k_emb);
    let embed_final_rat = embed(d, p, final_rat);
    let embed_mid2_rat3 = embed(d, p, mid2_rat3);
    let dd_k_to_target = d.lemma(
        p.equiv_trans,
        &[
            dd_k,
            embed_final_rat,
            embed_mid2_rat3,
            final_of_rat,
            final_equiv,
        ],
    );

    let refl_pow_xm = d.lemma(p.equiv_refl, &[pow_xm]);
    // per_m_proof : le pow_xm (embed (natDivSucc big_k m))
    d.lemma(
        p.le_congr,
        &[
            pow_xm,
            pow_xm,
            dd_k,
            embed_mid2_rat3,
            refl_pow_xm,
            dd_k_to_target,
            pow_le_kdd,
        ],
    )
}

/// `CReal.pow_le_natDivSucc_of_lt`. See the field documentation
/// ([`super::CRealPrelude::pow_le_nat_div_succ_of_lt`]) for the statement.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_pow_le_nat_div_succ_of_lt(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hx0_ty = cle(d, p, zero_c, x);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);

    let hlt_ty = d.const_app(p.lt, &[x, one_c]);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);

    // predicate := λK, ∀m, le (pow x m) (embed (natDivSucc K m))
    let predicate = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let pow_xm = d.const_app(p.pow, &[x, m]);
        let bound_rat = d.const_app(rat.nat_div_succ, &[k, m]);
        let bound = embed(d, p, bound_rat);
        let body = cle(d, p, pow_xm, bound);
        let inner = d.pi_fv(m_fv, nat, body);
        d.lam_fv(k_fv, nat, inner)
    };
    let target = {
        let one_level = d.level_one();
        let exists_name = rat.int.logic.exists_;
        let exists_ = d.kernel().const_(exists_name, vec![one_level]);
        d.apply(exists_, &[nat, predicate])
    };

    let minor_q = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let zero_r = rzero(d, rat);
        let positive_ty = rlt(d, rat, zero_r, q);
        let q_emb_ty = embed(d, p, q);
        let x_plus_q_ty = cadd(d, p, x, q_emb_ty);
        let bounded_ty = cle(d, p, x_plus_q_ty, one_c);
        let witness_ty = d.and(positive_ty, bounded_ty);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);

        let body = {
            let (hqpos, hle) = gap_halves(d, p, x, one_c, q, w);
            let q_emb = embed(d, p, q);

            // ---- pos_bound_of_lt(q_emb) -> k3, h_pb : le (embed (natDivSucc 1 k3)) q_emb ----
            let zero_lt_q_emb = d.lemma(p.of_rat_pos, &[q, hqpos]);
            let ex_pb = d.lemma(p.pos_bound_of_lt, &[q_emb, zero_lt_q_emb]);
            let pb_predicate = {
                let k2_fv = d.fresh_fvar();
                let k2 = d.kernel().fvar(k2_fv);
                let ty = d.const_app(p.pos_bound, &[q_emb, k2]);
                d.lam_fv(k2_fv, nat, ty)
            };

            let minor_k = {
                let k3_fv = d.fresh_fvar();
                let k3 = d.kernel().fvar(k3_fv);
                let h_pb_ty = d.const_app(p.pos_bound, &[q_emb, k3]);
                let h_pb_fv = d.fresh_fvar();
                let h_pb = d.kernel().fvar(h_pb_fv);

                let body_k = {
                    let m_fv = d.fresh_fvar();
                    let m = d.kernel().fvar(m_fv);
                    let per_m_proof =
                        pow_le_nat_div_succ_gap_leaf(d, p, x, hx0, q, hle, k3, h_pb, m);
                    let per_m = d.lam_fv(m_fv, nat, per_m_proof);
                    let big_k = d.succ(k3);
                    exists_nat_intro(d, p, predicate, big_k, per_m)
                };

                let with_h_pb = d.lam_fv(h_pb_fv, h_pb_ty, body_k);
                d.lam_fv(k3_fv, nat, with_h_pb)
            };

            let _ = pb_predicate;
            exists_elim(d, pb_predicate, target, ex_pb, minor_k)
        };

        let with_w = d.lam_fv(w_fv, witness_ty, body);
        let rat_carrier_q = rat_ty(d);
        d.lam_fv(q_fv, rat_carrier_q, with_w)
    };

    let carrier = creal_ty(d, p);
    let value = {
        let body = gap_elim(d, p, x, one_c, target, hlt, minor_q);
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, body);
        let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_hlt);
        d.lam_fv(x_fv, carrier, with_hx0)
    };
    let ty = {
        let after_hlt = d.arrow(hlt_ty, target);
        let after_hx0 = d.arrow(hx0_ty, after_hlt);
        d.pi_fv(x_fv, carrier, after_hx0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_le_nat_div_succ_of_lt,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.pow_le_natDivSucc_of_gap`. See the field documentation
/// ([`super::CRealPrelude::pow_le_nat_div_succ_of_gap`]) for the statement.
///
/// Nothing but [`pow_le_nat_div_succ_gap_leaf`] under six binders: the whole
/// content is shared with [`declare_pow_le_nat_div_succ_of_lt`], which
/// differs only by manufacturing `(q, k3)` from `lt x one` and then hiding
/// the resulting witness behind an `Exists.intro`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_pow_le_nat_div_succ_of_gap(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hx0_ty = cle(d, p, zero_c, x);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let q_emb = embed(d, p, q);
    let x_plus_q = cadd(d, p, x, q_emb);
    let hle_ty = cle(d, p, x_plus_q, one_c);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let k3_fv = d.fresh_fvar();
    let k3 = d.kernel().fvar(k3_fv);
    let h_pb_ty = d.const_app(p.pos_bound, &[q_emb, k3]);
    let h_pb_fv = d.fresh_fvar();
    let h_pb = d.kernel().fvar(h_pb_fv);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let leaf = pow_le_nat_div_succ_gap_leaf(d, p, x, hx0, q, hle, k3, h_pb, m);

    let big_k = d.succ(k3);
    let claim = {
        let pow_xm = d.const_app(p.pow, &[x, m]);
        let bound_rat = d.const_app(rat.nat_div_succ, &[big_k, m]);
        let bound = embed(d, p, bound_rat);
        cle(d, p, pow_xm, bound)
    };

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, claim);
        let with_hpb = d.pi_fv(h_pb_fv, h_pb_ty, over_m);
        let with_k3 = d.pi_fv(k3_fv, nat, with_hpb);
        let with_hle = d.pi_fv(hle_fv, hle_ty, with_k3);
        let with_q = d.pi_fv(q_fv, rat_carrier, with_hle);
        let with_hx0 = d.pi_fv(hx0_fv, hx0_ty, with_q);
        d.pi_fv(x_fv, carrier, with_hx0)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, leaf);
        let with_hpb = d.lam_fv(h_pb_fv, h_pb_ty, over_m);
        let with_k3 = d.lam_fv(k3_fv, nat, with_hpb);
        let with_hle = d.lam_fv(hle_fv, hle_ty, with_k3);
        let with_q = d.lam_fv(q_fv, rat_carrier, with_hle);
        let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_q);
        d.lam_fv(x_fv, carrier, with_hx0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_le_nat_div_succ_of_gap,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.ratioDecayBound` -- the ratio-test decay induction, `f(k) ≤ f(0)·rᵏ`.
// ---------------------------------------------------------------------------

/// `CReal.ratioDecayBound`. See the field documentation
/// ([`super::CRealPrelude::ratio_decay_bound`]) for the statement and the
/// derivation.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_ratio_decay_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let zero_c = czero(d, p);
    let h0r_ty = cle(d, p, zero_c, r);
    let h0r_fv = d.fresh_fvar();
    let h0r = d.kernel().fvar(h0r_fv);

    // hdec_ty := ∀ n, le (f (succ n)) (mul r (f n))
    let hdec_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let succ_n = d.succ(n);
        let f_succ_n = d.apply(f, &[succ_n]);
        let f_n = d.apply(f, &[n]);
        let r_fn = cmul(d, p, r, f_n);
        let body = cle(d, p, f_succ_n, r_fn);
        d.pi_fv(n_fv, nat, body)
    };
    let hdec_fv = d.fresh_fvar();
    let hdec = d.kernel().fvar(hdec_fv);

    let zero_nat = d.num(0);
    let f0 = d.apply(f, &[zero_nat]);

    // motive(v) := le (f v) (mul f0 (pow r v))
    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let fv_ = d.apply(f, &[v]);
        let pow_rv = d.const_app(p.pow, &[r, v]);
        let bound = cmul(d, p, f0, pow_rv);
        cle(d, p, fv_, bound)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            // base: le f0 (mul f0 one) -- target `mul f0 (pow r 0)` is defeq
            // to `mul f0 one` since `pow` ι-reduces at 0.
            let one_c = d.kernel().const_(p.one, vec![]);
            let f0_one = cmul(d, p, f0, one_c);
            let refl_f0 = d.lemma(p.equiv_refl, &[f0]);
            let mul_one_f0 = d.lemma(p.mul_one, &[f0]); // Equiv f0_one f0
            let hce = d.lemma(p.equiv_symm, &[f0_one, f0, mul_one_f0]); // Equiv f0 f0_one
            let base = d.lemma(p.le_refl, &[f0]);
            d.lemma(p.le_congr, &[f0, f0, f0, f0_one, refl_f0, hce, base])
        },
        &|d, j, ih| {
            // ih : le (f j) (mul f0 (pow r j))
            let pow_rj = d.const_app(p.pow, &[r, j]);
            let bound_j = cmul(d, p, f0, pow_rj);
            let f_j = d.apply(f, &[j]);
            let f_succ_j = {
                let sj = d.succ(j);
                d.apply(f, &[sj])
            };

            // raw1 : le (mul r (f j)) (mul r bound_j)
            let raw1 = d.lemma(p.mul_le_mul_of_nonneg_left, &[r, f_j, bound_j, h0r, ih]);
            let r_fj = cmul(d, p, r, f_j);
            let a_term = cmul(d, p, r, bound_j); // r * (f0 * pow_rj)

            // hdec_j : le (f (succ j)) (mul r (f j))
            let hdec_j = d.apply(hdec, &[j]);

            let chained = d.lemma(p.le_trans, &[f_succ_j, r_fj, a_term, hdec_j, raw1]);

            // Equiv chain: a_term ~ f0 * (pow_rj * r)  [(pow r (succ j)) ι's
            // recursive factor on the RIGHT, so this is the target shape].
            let r_f0 = cmul(d, p, r, f0);
            let b1 = cmul(d, p, r_f0, pow_rj);
            let assoc1 = d.lemma(p.mul_assoc, &[r, f0, pow_rj]); // Equiv b1 a_term
            let e1 = d.lemma(p.equiv_symm, &[b1, a_term, assoc1]); // Equiv a_term b1

            let f0_r = cmul(d, p, f0, r);
            let b2 = cmul(d, p, f0_r, pow_rj);
            let comm1 = d.lemma(p.mul_comm, &[r, f0]); // Equiv r_f0 f0_r
            let refl_prj = d.lemma(p.equiv_refl, &[pow_rj]);
            let e2 = d.lemma(p.mul_congr, &[r_f0, f0_r, pow_rj, pow_rj, comm1, refl_prj]); // Equiv b1 b2

            let r_prj = cmul(d, p, r, pow_rj);
            let b3 = cmul(d, p, f0, r_prj);
            let e3 = d.lemma(p.mul_assoc, &[f0, r, pow_rj]); // Equiv b2 b3

            let prj_r = cmul(d, p, pow_rj, r);
            let b4 = cmul(d, p, f0, prj_r);
            let comm2 = d.lemma(p.mul_comm, &[r, pow_rj]); // Equiv r_prj prj_r
            let refl_f0b = d.lemma(p.equiv_refl, &[f0]);
            let e4 = d.lemma(p.mul_congr, &[f0, f0, r_prj, prj_r, refl_f0b, comm2]); // Equiv b3 b4

            let hce = echain(d, p, a_term, &[(b1, e1), (b2, e2), (b3, e3), (b4, e4)]);

            let refl_target = d.lemma(p.equiv_refl, &[f_succ_j]);
            d.lemma(
                p.le_congr,
                &[f_succ_j, f_succ_j, a_term, b4, refl_target, hce, chained],
            )
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_hdec = d.arrow(hdec_ty, inner);
        let with_h0r = d.arrow(h0r_ty, with_hdec);
        let with_r = d.pi_fv(r_fv, carrier, with_h0r);
        d.pi_fv(f_fv, fn_ty, with_r)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_hdec = d.lam_fv(hdec_fv, hdec_ty, inner);
        let with_h0r = d.lam_fv(h0r_fv, h0r_ty, with_hdec);
        let with_r = d.lam_fv(r_fv, carrier, with_h0r);
        d.lam_fv(f_fv, fn_ty, with_r)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ratio_decay_bound,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.invLeOfPosBound` -- a `PosBound`-witnessed inverse is bounded by a
// whole number computed from its own modulus.
// ---------------------------------------------------------------------------

/// `CReal.invLeOfPosBound`. See the field documentation
/// ([`super::CRealPrelude::inv_le_of_pos_bound`]) for the statement and the
/// derivation.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_inv_le_of_pos_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rat = p.rat;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let h_ty = pos_bound_of(d, p, x, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let succ_k = d.succ(k);

    let q_rat = d.const_app(rat.nat_div_succ, &[one_nat, k]);
    let c_rat = d.const_app(rat.nat_div_succ, &[succ_k, zero_nat]);

    let q = embed(d, p, q_rat);
    let c_embed = embed(d, p, c_rat);
    let c_ofnat = d.const_app(p.of_nat, &[succ_k]);

    let iv = cinv(d, p, x, k, h);

    // h_pos_q : Rat.lt Rat.zero (natDivSucc 1 k), from Nat.le 1 1.
    let le11 = {
        let np = d.prelude();
        d.const_app(np.le_refl, &[one_nat])
    };
    let h_pos_q = d.lemma(rat.nat_div_succ_pos, &[one_nat, k, le11]);

    // h_cancel : Eq Rat (mul q_rat (Rat.inv q_rat)) Rat.one
    let h_cancel = d.lemma(rat.mul_inv_cancel, &[q_rat, h_pos_q]);
    // h_inv_eq : Eq Rat (Rat.inv q_rat) c_rat
    let h_inv_eq = d.lemma(rat.inv_nat_div_succ, &[k]);

    let inv_q_rat = d.const_app(rat.inv, &[q_rat]);
    let rone_expr = rone(d, rat);
    // rat_prod_eq_one : Eq Rat (mul q_rat c_rat) Rat.one
    let rat_prod_eq_one = rat_eq_rewrite(d, inv_q_rat, c_rat, h_inv_eq, h_cancel, &|d, t| {
        let lhs = rmul(d, q_rat, t);
        req(d, lhs, rone_expr)
    });

    let mul_qc_rat = rmul(d, q_rat, c_rat);
    // hqc_embed : Equiv (embed mul_qc_rat) (embed rone_expr)
    let hqc_embed = embed_eq_to_equiv(d, p, mul_qc_rat, rone_expr, rat_prod_eq_one);

    // ofrm : Equiv (mul q c_embed) (embed mul_qc_rat)
    let ofrm = d.lemma(p.of_rat_mul, &[q_rat, c_rat]);

    let mul_q_c = cmul(d, p, q, c_embed);
    let embed_mul_qc = embed(d, p, mul_qc_rat);
    let embed_one_rat = embed(d, p, rone_expr);
    // hqc : Equiv (mul q c_embed) (embed rone_expr)  -- defeq to `one`.
    let hqc = d.lemma(
        p.equiv_trans,
        &[mul_q_c, embed_mul_qc, embed_one_rat, ofrm, hqc_embed],
    );

    // c_nonneg : le zero c_embed
    let c_nonneg = {
        let zero_r = rzero(d, rat);
        let c_rat_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[succ_k, zero_nat]);
        d.lemma(p.of_rat_le, &[zero_r, c_rat, c_rat_nonneg])
    };

    // step_a : le (mul q c_embed) (mul x c_embed), from `h : PosBound x k`
    // unfolding to `le q x` and `c_nonneg`.
    let step_a = mul_le_mul_of_nonneg_right(d, p, q, x, c_embed, c_nonneg, h);

    // h_one_le_xc : le one (mul x c_embed), transporting step_a's LHS across
    // `hqc`.
    let mul_x_c = cmul(d, p, x, c_embed);
    let one_c = d.kernel().const_(p.one, vec![]);
    let refl_mxc = d.lemma(p.equiv_refl, &[mul_x_c]);
    let h_one_le_xc = d.lemma(
        p.le_congr,
        &[mul_q_c, one_c, mul_x_c, mul_x_c, hqc, refl_mxc, step_a],
    );

    // h_mul_le : le (mul x iv) (mul x c_embed), transporting h_one_le_xc's
    // LHS across `mul_inv_cancel`, symmetrised.
    let cancel_xk = d.lemma(p.mul_inv_cancel, &[x, k, h]); // Equiv (mul x iv) one_c
    let mul_x_iv = cmul(d, p, x, iv);
    let symm_cancel = d.lemma(p.equiv_symm, &[mul_x_iv, one_c, cancel_xk]); // Equiv one_c mul_x_iv
    let refl_mxc2 = d.lemma(p.equiv_refl, &[mul_x_c]);
    let h_mul_le = d.lemma(
        p.le_congr,
        &[
            one_c,
            mul_x_iv,
            mul_x_c,
            mul_x_c,
            symm_cancel,
            refl_mxc2,
            h_one_le_xc,
        ],
    );

    // final_le : le iv c_embed, cancelling x via the SAME witness (k, h)
    // `inv` itself takes.
    let final_le = d.lemma(p.le_of_mul_le_mul_left, &[x, iv, c_embed, k, h, h_mul_le]);

    let ty = {
        let concl = cle(d, p, iv, c_ofnat);
        let with_h = d.pi_fv(h_fv, h_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, with_h);
        d.pi_fv(x_fv, carrier, with_k)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, h_ty, final_le);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(x_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.inv_le_of_pos_bound,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.geomYBound` -- generalizing `geomHalfInvLeafBound`
// (`exponential.rs`, concrete base 1/2 only) to a symbolic ratio `x` and a
// symbolic `PosBound (1 - x) k` witness.
// ---------------------------------------------------------------------------

/// The shared, non-existential leaf of `CReal.geomYBound` and
/// `CReal.geomYBoundRaw`: given `hk1 : ∀ m, le (pow x m) (ofRat (natDivSucc
/// k1 m))`, a proof of
/// `le (mul (inv (add one (neg x)) k h) (pow x a))
///     (ofRat (natDivSucc (Nat.mul (Nat.succ k) k1) a))`.
///
/// `iv · xᵃ ≤ (k+1) · xᵃ ≤ (k+1) · (k1/(a+1))`, the last fused into one
/// `natDivSucc` by `Rat.natDivSucc_mul`. Nothing here is existential: the
/// only reason [`declare_geom_y_bound`] wraps it in an `Exists` is that its
/// own `k1` comes from eliminating
/// [`super::CRealPrelude::pow_le_nat_div_succ_of_lt`]'s `∃ K`.
#[allow(clippy::too_many_arguments)]
fn geom_y_bound_leaf(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    hx0: ExprId,
    k: ExprId,
    h: ExprId,
    k1: ExprId,
    hk1: ExprId,
    a: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero_nat = d.num(0);
    let one_c = d.kernel().const_(p.one, vec![]);
    let neg_x = cneg(d, p, x);
    let a_real = cadd(d, p, one_c, neg_x);
    let iv = cinv(d, p, a_real, k, h);
    let hinv = d.lemma(p.inv_le_of_pos_bound, &[a_real, k, h]);
    // hinv : le iv (ofNat (succ k)) -- defeq to `le iv embed_succk` through
    // `CReal.ofNat`'s own definition (`archimedean.rs`).
    let succ_k = d.succ(k);
    let succk_rat = d.const_app(rat.nat_div_succ, &[succ_k, zero_nat]);
    let embed_succk = embed(d, p, succk_rat);
    let big_k_val = NatOps::mul(d, succ_k, k1);

    let pow_xa = d.const_app(p.pow, &[x, a]);
    let hk1_a = d.apply(hk1, &[a]);
    // hk1_a : le (pow x a) (ofRat (natDivSucc k1 a))

    let pow_nonneg_a = d.lemma(p.pow_nonneg, &[x, hx0, a]);
    // pow_nonneg_a : le zero (pow x a)

    // Step A: iv ≤ embed_succk (via hinv, defeq bridge), times
    // nonneg `pow_xa` on the right.
    let step_a = mul_le_mul_of_nonneg_right(d, p, iv, embed_succk, pow_xa, pow_nonneg_a, hinv);
    // step_a : le (mul iv pow_xa) (mul embed_succk pow_xa)

    // Step B: `pow_xa ≤ embed (natDivSucc k1 a)`, times nonneg
    // `embed_succk` on the left.
    let c_nonneg = {
        let succk_rat_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[succ_k, zero_nat]);
        let zero_r = rzero(d, rat);
        d.lemma(p.of_rat_le, &[zero_r, succk_rat, succk_rat_nonneg])
    };
    let k1a_rat = d.const_app(rat.nat_div_succ, &[k1, a]);
    let embed_k1a = embed(d, p, k1a_rat);
    let step_b = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[embed_succk, pow_xa, embed_k1a, c_nonneg, hk1_a],
    );
    // step_b : le (mul embed_succk pow_xa) (mul embed_succk embed_k1a)

    let mul_iv_pow = cmul(d, p, iv, pow_xa);
    let mul_c_pow = cmul(d, p, embed_succk, pow_xa);
    let mul_c_k1a = cmul(d, p, embed_succk, embed_k1a);
    let chained = d.lemma(
        p.le_trans,
        &[mul_iv_pow, mul_c_pow, mul_c_k1a, step_a, step_b],
    );
    // chained : le mul_iv_pow mul_c_k1a

    // `Equiv mul_c_k1a (embed (natDivSucc ((succ k)*k1) a))`, via
    // `Rat.natDivSucc_mul` fusing `natDivSucc (succ k) 0` and
    // `natDivSucc k1 a` into one `natDivSucc`.
    let target_rat = d.const_app(rat.nat_div_succ, &[big_k_val, a]);
    let of_rat_mul_eq = d.lemma(p.of_rat_mul, &[succk_rat, k1a_rat]);
    // of_rat_mul_eq : Equiv mul_c_k1a (embed (rmul succk_rat k1a_rat))
    let prod_rat = rmul(d, succk_rat, k1a_rat);
    let fuse_eq = d.lemma(rat.nat_div_succ_mul, &[succ_k, k1, a]);
    // fuse_eq : Eq prod_rat target_rat
    let embed_prod_eq = embed_eq_to_equiv(d, p, prod_rat, target_rat, fuse_eq);
    // embed_prod_eq : Equiv (embed prod_rat) (embed target_rat)
    let embed_prod = embed(d, p, prod_rat);
    let embed_target = embed(d, p, target_rat);
    let combined = d.lemma(
        p.equiv_trans,
        &[
            mul_c_k1a,
            embed_prod,
            embed_target,
            of_rat_mul_eq,
            embed_prod_eq,
        ],
    );
    // combined : Equiv mul_c_k1a embed_target

    let refl_lhs = d.lemma(p.equiv_refl, &[mul_iv_pow]);
    // final_le_a : le mul_iv_pow embed_target
    d.lemma(
        p.le_congr,
        &[
            mul_iv_pow,
            mul_iv_pow,
            mul_c_k1a,
            embed_target,
            refl_lhs,
            combined,
            chained,
        ],
    )
}

/// `CReal.geomYBound`. See the field documentation
/// ([`super::CRealPrelude::geom_y_bound`]) for the statement and the
/// derivation.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_geom_y_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hx0_ty = cle(d, p, zero_c, x);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);
    let hlt_ty = d.const_app(p.lt, &[x, one_c]);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);

    let neg_x = cneg(d, p, x);
    let a_real = cadd(d, p, one_c, neg_x); // a_real = 1 - x
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let h_ty = pos_bound_of(d, p, a_real, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let iv = cinv(d, p, a_real, k, h);
    let succ_k = d.succ(k);

    // `predicate1(K1) := ∀ m, le (pow x m) (ofRat (natDivSucc K1 m))` --
    // reconstructed verbatim in shape to `declare_pow_le_nat_div_succ_of_lt`'s
    // own bound predicate, so `exists_elim` accepts it against `ex_pow`'s own
    // substituted type (same technique that function uses for its own nested
    // `pos_bound_of_lt` elimination).
    let predicate1 = {
        let k1_fv = d.fresh_fvar();
        let k1 = d.kernel().fvar(k1_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let pow_xm = d.const_app(p.pow, &[x, m]);
        let bound_rat = d.const_app(rat.nat_div_succ, &[k1, m]);
        let bound = embed(d, p, bound_rat);
        let body = cle(d, p, pow_xm, bound);
        let inner = d.pi_fv(m_fv, nat, body);
        d.lam_fv(k1_fv, nat, inner)
    };
    let ex_pow = d.lemma(p.pow_le_nat_div_succ_of_lt, &[x, hx0, hlt]);

    // Target: `∃ K, ∀ a, le (mul iv (pow x a)) (ofRat (natDivSucc K a))`.
    let target_predicate = {
        let bigk_fv = d.fresh_fvar();
        let bigk = d.kernel().fvar(bigk_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let pow_xa = d.const_app(p.pow, &[x, a]);
        let mul_iv_pow = cmul(d, p, iv, pow_xa);
        let bound_rat = d.const_app(rat.nat_div_succ, &[bigk, a]);
        let bound = embed(d, p, bound_rat);
        let body = cle(d, p, mul_iv_pow, bound);
        let inner = d.pi_fv(a_fv, nat, body);
        d.lam_fv(bigk_fv, nat, inner)
    };
    let target = {
        let one_level = d.level_one();
        let exists_name = rat.int.logic.exists_;
        let exists_ = d.kernel().const_(exists_name, vec![one_level]);
        d.apply(exists_, &[nat, target_predicate])
    };

    // `minor : ∀ K1, (∀ m, le (pow x m) (ofRat (natDivSucc K1 m))) → target`,
    // with witness `K := (succ k)*K1`.
    let minor = {
        let k1_fv = d.fresh_fvar();
        let k1 = d.kernel().fvar(k1_fv);
        let hk1_ty = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let pow_xm = d.const_app(p.pow, &[x, m]);
            let bound_rat = d.const_app(rat.nat_div_succ, &[k1, m]);
            let bound = embed(d, p, bound_rat);
            let body = cle(d, p, pow_xm, bound);
            d.pi_fv(m_fv, nat, body)
        };
        let hk1_fv = d.fresh_fvar();
        let hk1 = d.kernel().fvar(hk1_fv);

        let big_k_val = NatOps::mul(d, succ_k, k1);

        let body = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let final_le_a = geom_y_bound_leaf(d, p, x, hx0, k, h, k1, hk1, a);
            d.lam_fv(a_fv, nat, final_le_a)
        };

        let proof_for_k1 = exists_nat_intro(d, p, target_predicate, big_k_val, body);
        let with_hk1 = d.lam_fv(hk1_fv, hk1_ty, proof_for_k1);
        d.lam_fv(k1_fv, nat, with_hk1)
    };

    let proof_body = exists_elim(d, predicate1, target, ex_pow, minor);

    let ty = {
        let inner = d.pi_fv(h_fv, h_ty, target);
        let with_k = d.pi_fv(k_fv, nat, inner);
        let after_hlt = d.arrow(hlt_ty, with_k);
        let after_hx0 = d.arrow(hx0_ty, after_hlt);
        d.pi_fv(x_fv, carrier, after_hx0)
    };
    let value = {
        let inner = d.lam_fv(h_fv, h_ty, proof_body);
        let with_k = d.lam_fv(k_fv, nat, inner);
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, with_k);
        let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_hlt);
        d.lam_fv(x_fv, carrier, with_hx0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_y_bound,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.geomYBoundRaw`. See the field documentation
/// ([`super::CRealPrelude::geom_y_bound_raw`]) for the statement.
///
/// Shares [`geom_y_bound_leaf`] verbatim with [`declare_geom_y_bound`]; the
/// only difference between the two theorems is that this one keeps `(k1,
/// hk1)` as parameters and the witness `(Nat.succ k)*k1` visible in the
/// conclusion, where that one eliminates `pow_le_natDivSucc_of_lt`'s `∃ K1`
/// and re-wraps the result in an `Exists.intro`. Note `lt x one` does not
/// appear: it was needed only to manufacture `k1`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_geom_y_bound_raw(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hx0_ty = cle(d, p, zero_c, x);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);

    let neg_x = cneg(d, p, x);
    let a_real = cadd(d, p, one_c, neg_x);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let h_ty = pos_bound_of(d, p, a_real, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let iv = cinv(d, p, a_real, k, h);

    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let hk1_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let pow_xm = d.const_app(p.pow, &[x, m]);
        let bound_rat = d.const_app(rat.nat_div_succ, &[k1, m]);
        let bound = embed(d, p, bound_rat);
        let body = cle(d, p, pow_xm, bound);
        d.pi_fv(m_fv, nat, body)
    };
    let hk1_fv = d.fresh_fvar();
    let hk1 = d.kernel().fvar(hk1_fv);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let leaf = geom_y_bound_leaf(d, p, x, hx0, k, h, k1, hk1, a);

    let succ_k = d.succ(k);
    let big_k_val = NatOps::mul(d, succ_k, k1);
    let claim = {
        let pow_xa = d.const_app(p.pow, &[x, a]);
        let mul_iv_pow = cmul(d, p, iv, pow_xa);
        let bound_rat = d.const_app(rat.nat_div_succ, &[big_k_val, a]);
        let bound = embed(d, p, bound_rat);
        cle(d, p, mul_iv_pow, bound)
    };

    let ty = {
        let over_a = d.pi_fv(a_fv, nat, claim);
        let with_hk1 = d.pi_fv(hk1_fv, hk1_ty, over_a);
        let with_k1 = d.pi_fv(k1_fv, nat, with_hk1);
        let with_h = d.pi_fv(h_fv, h_ty, with_k1);
        let with_k = d.pi_fv(k_fv, nat, with_h);
        let with_hx0 = d.pi_fv(hx0_fv, hx0_ty, with_k);
        d.pi_fv(x_fv, carrier, with_hx0)
    };
    let value = {
        let over_a = d.lam_fv(a_fv, nat, leaf);
        let with_hk1 = d.lam_fv(hk1_fv, hk1_ty, over_a);
        let with_k1 = d.lam_fv(k1_fv, nat, with_hk1);
        let with_h = d.lam_fv(h_fv, h_ty, with_k1);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_k);
        d.lam_fv(x_fv, carrier, with_hx0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_y_bound_raw,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.geomCauchyOfLt` -- geometric-series Cauchyness at a GENERAL ratio
// `0 ≤ x < 1`, mirroring `exponential.rs::declare_geom_cauchy_ordered_half` /
// `declare_geom_cauchy` but parametrized by [`declare_geom_y_bound`]'s general
// `x`/`k`/`h` and its outer existential witness `bigK` (carried here as an
// explicit universally-quantified hypothesis `hK`) in place of the concrete
// base-`1/2` leaf bound `geomHalfInvLeafBound` and the literal `7`.
//
// The two theorems below are the direct generalization of
// `geomCauchyOrderedHalf`/`geomCauchy`: every leg of the widening/fusion
// arithmetic that came from `CReal.regular`'s own `1/(n+1)` modulus or from
// `geom_pair_within`'s own fixed `natDivSucc 2 b` leaf is untouched (none of
// it depends on the base), and the ONE leg that was pinned to the literal `2`
// (`geomHalfInvLeafBound`'s own leaf bound) becomes the symbolic `bigK` this
// file's `geomYBound` supplies. The final fused modulus is `(bigK+1)+7` on
// BOTH sides (`bigK+1` from fusing the `a`-side leaf with the regularity
// constant `natDivSucc 1 a`, `7` unchanged from the `b`-side, whichever is
// smaller padded up to the sum via `Rat.natDivSucc_le_add_left` -- never via a
// literal coincidence like `geomCauchy`'s own `3+4=7`, since `bigK` is
// symbolic).
// ---------------------------------------------------------------------------

/// `Nat.add bigK (Nat.num 1)`, i.e. `bigK+1` -- the `a`-side fused numerator
/// [`declare_geom_cauchy_of_lt_ordered`] builds via [`fuse_same_index`] and
/// [`declare_geom_cauchy_of_lt`] must reconstruct externally (to state
/// `Cauchy`'s own witness), kept as a single Rust function so both sites
/// build the identical `ExprId`.
fn geom_cauchy_of_lt_big_k1(d: &mut IntDev<'_>, bigk: ExprId) -> ExprId {
    let one_nat = d.num(1);
    d.add(bigk, one_nat)
}

/// `(bigK+1)+7` -- the single Nat modulus [`declare_geom_cauchy_of_lt_ordered`]'s
/// bound uses on BOTH sides, as a function of `geomYBound`'s own witness
/// `bigK`. See [`geom_cauchy_of_lt_big_k1`]'s own doc for why this is a
/// shared Rust function rather than inlined at each call site.
fn geom_cauchy_of_lt_k_final(d: &mut IntDev<'_>, bigk: ExprId) -> ExprId {
    let big_k1 = geom_cauchy_of_lt_big_k1(d, bigk);
    let seven_nat = d.num(7);
    d.add(big_k1, seven_nat)
}

/// `CReal.geomCauchyOfLtOrdered`. See the module documentation just above for
/// the derivation: verbatim in *shape* to
/// `exponential.rs::declare_geom_cauchy_ordered_half`, generalized from the
/// concrete base `1/2` (`k := 1`, leaf bound `natDivSucc 2 a`, final modulus
/// the literal `7`) to a symbolic `x`/`k`/`h` and a symbolic leaf-bound
/// witness `(bigK, hK)` supplied by [`declare_geom_y_bound`]'s own outer
/// existential.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_geom_cauchy_of_lt_ordered(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hx0_ty = cle(d, p, zero_c, x);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);

    let neg_x = cneg(d, p, x);
    let a_real = cadd(d, p, one_c, neg_x); // a_real = 1 - x
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let h_ty = pos_bound_of(d, p, a_real, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let inv_expr = cinv(d, p, a_real, k, h);

    let bigk_fv = d.fresh_fvar();
    let bigk = d.kernel().fvar(bigk_fv);
    let hk_ty = {
        let a0_fv = d.fresh_fvar();
        let a0 = d.kernel().fvar(a0_fv);
        let pow_xa0 = d.const_app(p.pow, &[x, a0]);
        let mul_iv_pow0 = cmul(d, p, inv_expr, pow_xa0);
        let bound_rat0 = div_succ_var(d, p, bigk, a0);
        let bound0 = embed(d, p, bound_rat0);
        let body0 = cle(d, p, mul_iv_pow0, bound0);
        d.pi_fv(a0_fv, nat, body0)
    };
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let f = pow_fn(d, p, x);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hle_ty = d.le(a, b);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let raw = d.lemma(p.geom_pair_within, &[x, hx0, k, h, a, b, hle]);

    // Reconstruct `diff`/`total` exactly as `geom_pair_within`'s own body
    // builds them, so `weaken` below sees the SAME `bound` its `proof`
    // argument (`raw`) actually carries.
    let sum_f_b = d.const_app(p.sum_range, &[f, b]);
    let sum_f_a = d.const_app(p.sum_range, &[f, a]);
    let y_pt = sample(d, p, sum_f_b, b);
    let z_pt = sample(d, p, sum_f_a, a);
    let diff = rsub(d, rat, y_pt, z_pt);

    let t = shift(d, b);
    let t1 = div_succ(d, p, 1, t);
    let b1 = div_succ(d, p, 1, b);
    let a1 = div_succ(d, p, 1, a);
    let pow_xa = d.const_app(p.pow, &[x, a]);
    let y_a = cmul(d, p, inv_expr, pow_xa);
    let v = sample(d, p, y_a, b);
    let b2 = div_succ(d, p, 2, b);

    let bxy = modulus(d, p, t, b);
    let byz = radd(d, v, b2);
    let bzw = modulus(d, p, a, t);
    let bxy_byz = radd(d, bxy, byz);
    let total = radd(d, bxy_byz, bzw);

    // --- widen: `t1 -> b1` (twice) and `v -> vb` -------------------------
    let one_nat = d.num(1);
    let wt = d.lemma(rat.nat_div_succ_le_scaled, &[one_nat, one_nat, b]);
    // wt : le t1 b1

    let hv_at_a = d.apply(hk, &[a]);
    // hv_at_a : le y_a (embed (natDivSucc bigK a))
    let raw_v = d.apply(hv_at_a, &[b]);
    // raw_v : (defeq) Rat.le (Rat.sub v a_k) b2
    let a_k = div_succ_var(d, p, bigk, a);
    let y_leaf_le = d.lemma(rat.le_of_sub_le, &[v, a_k, b2, raw_v]);
    // y_leaf_le : le v (radd a_k b2) = le v vb
    let vb = radd(d, a_k, b2);

    let bxy_w = radd(d, b1, b1);
    let byz_w = radd(d, vb, b2);
    let bzw_w = radd(d, a1, b1);

    let refl_b1 = d.lemma(rat.le_refl, &[b1]);
    let refl_a1 = d.lemma(rat.le_refl, &[a1]);
    let refl_b2 = d.lemma(rat.le_refl, &[b2]);

    let step1 = d.lemma(rat.add_le_add, &[t1, b1, b1, b1, wt, refl_b1]);
    // step1 : le bxy bxy_w
    let step2 = d.lemma(rat.add_le_add, &[v, vb, b2, b2, y_leaf_le, refl_b2]);
    // step2 : le byz byz_w
    let step3 = d.lemma(rat.add_le_add, &[bxy, bxy_w, byz, byz_w, step1, step2]);
    // step3 : le bxy_byz (radd bxy_w byz_w)
    let step4 = d.lemma(rat.add_le_add, &[a1, a1, t1, b1, refl_a1, wt]);
    // step4 : le bzw bzw_w
    let bxy_byz_w = radd(d, bxy_w, byz_w);
    let order = d.lemma(
        rat.add_le_add,
        &[bxy_byz, bxy_byz_w, bzw, bzw_w, step3, step4],
    );
    // order : le total wider
    let wider = radd(d, bxy_byz_w, bzw_w);
    // wider = ((b1+b1)+(vb+b2))+(a1+b1) = ((b1+b1)+((a_k+b2)+b2))+(a1+b1)

    // --- reassociate + fuse: `wider` -> `natDivSucc (bigK+1) a + natDivSucc 7 b`,
    // then pad both to the common target `(bigK+1)+7` --------------------
    let m_right = radd(d, b2, b2); // b2+b2
    let m = radd(d, bxy_w, m_right); // (b1+b1)+(b2+b2)
    let a_k_plus_m_right = radd(d, a_k, m_right);

    let step_r1 = d.lemma(rat.add_assoc, &[a_k, b2, b2]);
    let s1_inner = radd(d, bxy_w, a_k_plus_m_right);
    let s1 = radd(d, s1_inner, bzw_w);
    let step_r1_lifted = rcongr(d, byz_w, a_k_plus_m_right, step_r1, &|d, t| {
        let inner = radd(d, bxy_w, t);
        radd(d, inner, bzw_w)
    });

    let bxy_w_plus_ak = radd(d, bxy_w, a_k);
    let step_r2 = assoc_rev_eq(d, p, bxy_w, a_k, m_right);
    let s2_inner = radd(d, bxy_w_plus_ak, m_right);
    let s2 = radd(d, s2_inner, bzw_w);
    let step_r2_lifted = rcongr(d, s1_inner, s2_inner, step_r2, &|d, t| radd(d, t, bzw_w));

    let ak_plus_bxy_w = radd(d, a_k, bxy_w);
    let step_r3 = d.lemma(rat.add_comm, &[bxy_w, a_k]);
    let s3_inner = radd(d, ak_plus_bxy_w, m_right);
    let s3 = radd(d, s3_inner, bzw_w);
    let step_r3_lifted = rcongr(d, bxy_w_plus_ak, ak_plus_bxy_w, step_r3, &|d, t| {
        let inner = radd(d, t, m_right);
        radd(d, inner, bzw_w)
    });

    let step_r4 = d.lemma(rat.add_assoc, &[a_k, bxy_w, m_right]);
    let ak_plus_m = radd(d, a_k, m);
    let s4 = radd(d, ak_plus_m, bzw_w);
    let step_r4_lifted = rcongr(d, s3_inner, ak_plus_m, step_r4, &|d, t| radd(d, t, bzw_w));

    let step_r5 = d.lemma(rat.add_assoc, &[a_k, m, bzw_w]);
    let m_plus_bzw_w = radd(d, m, bzw_w);
    let s5 = radd(d, a_k, m_plus_bzw_w);

    let step_r6 = assoc_rev_eq(d, p, m, a1, b1);
    let m_plus_a1 = radd(d, m, a1);
    let m_plus_a1_plus_b1 = radd(d, m_plus_a1, b1);
    let s6 = radd(d, a_k, m_plus_a1_plus_b1);
    let step_r6_lifted = rcongr(d, m_plus_bzw_w, m_plus_a1_plus_b1, step_r6, &|d, t| {
        radd(d, a_k, t)
    });

    let step_r7 = d.lemma(rat.add_comm, &[m, a1]);
    let a1_plus_m = radd(d, a1, m);
    let a1_plus_m_plus_b1 = radd(d, a1_plus_m, b1);
    let s7 = radd(d, a_k, a1_plus_m_plus_b1);
    let step_r7_lifted = rcongr(d, m_plus_a1, a1_plus_m, step_r7, &|d, t| {
        let inner = radd(d, t, b1);
        radd(d, a_k, inner)
    });

    let step_r8 = d.lemma(rat.add_assoc, &[a1, m, b1]);
    let m_plus_b1 = radd(d, m, b1);
    let a1_plus_m_plus_b1_r = radd(d, a1, m_plus_b1);
    let s8 = radd(d, a_k, a1_plus_m_plus_b1_r);
    let step_r8_lifted = rcongr(
        d,
        a1_plus_m_plus_b1,
        a1_plus_m_plus_b1_r,
        step_r8,
        &|d, t| radd(d, a_k, t),
    );

    let step_r9 = assoc_rev_eq(d, p, a_k, a1, m_plus_b1);
    let ak_plus_a1 = radd(d, a_k, a1);
    let s9 = radd(d, ak_plus_a1, m_plus_b1);

    let (a_k1, step_r10) = fuse_same_index(d, p, bigk, one_nat, a);
    // a_k1 = natDivSucc (bigK+1) a
    let s10 = radd(d, a_k1, m_plus_b1);
    let step_r10_lifted = rcongr(d, ak_plus_a1, a_k1, step_r10, &|d, t| radd(d, t, m_plus_b1));

    let (bb2, step_r11) = fuse_same_index(d, p, one_nat, one_nat, b);
    let bb2_plus_m_right = radd(d, bb2, m_right);
    let bb2_plus_m_right_plus_b1 = radd(d, bb2_plus_m_right, b1);
    let s11 = radd(d, a_k1, bb2_plus_m_right_plus_b1);
    let step_r11_lifted = rcongr(d, bxy_w, bb2, step_r11, &|d, t| {
        let inner_m = radd(d, t, m_right);
        let inner_mb1 = radd(d, inner_m, b1);
        radd(d, a_k1, inner_mb1)
    });

    let two_nat = d.num(2);
    let (bb4, step_r12) = fuse_same_index(d, p, two_nat, two_nat, b);
    let bb2_plus_bb4 = radd(d, bb2, bb4);
    let bb2_plus_bb4_plus_b1 = radd(d, bb2_plus_bb4, b1);
    let s12 = radd(d, a_k1, bb2_plus_bb4_plus_b1);
    let step_r12_lifted = rcongr(d, m_right, bb4, step_r12, &|d, t| {
        let inner_m = radd(d, bb2, t);
        let inner_mb1 = radd(d, inner_m, b1);
        radd(d, a_k1, inner_mb1)
    });

    let four_nat = d.num(4);
    let (bb6, step_r13) = fuse_same_index(d, p, two_nat, four_nat, b);
    let bb6_plus_b1 = radd(d, bb6, b1);
    let s13 = radd(d, a_k1, bb6_plus_b1);
    let step_r13_lifted = rcongr(d, bb2_plus_bb4, bb6, step_r13, &|d, t| {
        let inner_mb1 = radd(d, t, b1);
        radd(d, a_k1, inner_mb1)
    });

    let six_nat = d.num(6);
    let (b7, step_r14) = fuse_same_index(d, p, six_nat, one_nat, b);
    let s14 = radd(d, a_k1, b7);
    let step_r14_lifted = rcongr(d, bb6_plus_b1, b7, step_r14, &|d, t| radd(d, a_k1, t));

    let step_r15 = d.lemma(rat.add_comm, &[a_k1, b7]);
    let s15 = radd(d, b7, a_k1);

    let (_, wider_to_s15) = rchain(
        d,
        wider,
        &[
            (s1, step_r1_lifted),
            (s2, step_r2_lifted),
            (s3, step_r3_lifted),
            (s4, step_r4_lifted),
            (s5, step_r5),
            (s6, step_r6_lifted),
            (s7, step_r7_lifted),
            (s8, step_r8_lifted),
            (s9, step_r9),
            (s10, step_r10_lifted),
            (s11, step_r11_lifted),
            (s12, step_r12_lifted),
            (s13, step_r13_lifted),
            (s14, step_r14_lifted),
            (s15, step_r15),
        ],
    );

    let le_wider_s15 = {
        let refl_wider = d.lemma(rat.le_refl, &[wider]);
        rat_eq_rewrite(d, wider, s15, wider_to_s15, refl_wider, &|d, t| {
            rle(d, rat, wider, t)
        })
    };

    // Pad `a_k1` and `b7` (numerators `bigK+1` and `7`) up to the common
    // target `big_k1 + seven_nat`, unlike `geomCauchy`'s own literal `3+4=7`
    // coincidence -- `big_k1` is symbolic, so the two orders `big_k1+seven`
    // and `seven+big_k1` need an explicit `Nat.add_comm` bridge.
    let seven_nat = d.num(7);
    let big_k1 = geom_cauchy_of_lt_big_k1(d, bigk);
    let k_final = d.add(big_k1, seven_nat);

    let pad_a = d.lemma(rat.nat_div_succ_le_add_left, &[big_k1, seven_nat, a]);
    // pad_a : le a_k1 (natDivSucc k_final a)

    let seven_plus_bigk1 = d.add(seven_nat, big_k1);
    let np = d.prelude();
    let comm_proof = d.lemma(np.add_comm, &[seven_nat, big_k1]);
    // comm_proof : Eq Nat seven_plus_bigk1 k_final
    let pad_b_eq = nat_eq_to_rat(d, seven_plus_bigk1, k_final, comm_proof, &|d, t| {
        div_succ_var(d, p, t, b)
    });
    let pad_b_raw = d.lemma(rat.nat_div_succ_le_add_left, &[seven_nat, big_k1, b]);
    let nds_seven_plus_bigk1_b = div_succ_var(d, p, seven_plus_bigk1, b);
    let nds_k_final_b = div_succ_var(d, p, k_final, b);
    let pad_b = rat_eq_rewrite(
        d,
        nds_seven_plus_bigk1_b,
        nds_k_final_b,
        pad_b_eq,
        pad_b_raw,
        &|d, t| rle(d, rat, b7, t),
    );
    // pad_b : le b7 (natDivSucc k_final b)

    let nds_k_final_a = div_succ_var(d, p, k_final, a);
    let target_bound = radd(d, nds_k_final_b, nds_k_final_a);

    let le_s15_target = d.lemma(
        rat.add_le_add,
        &[b7, nds_k_final_b, a_k1, nds_k_final_a, pad_b, pad_a],
    );
    let le_wider_target = d.lemma(
        rat.le_trans,
        &[wider, s15, target_bound, le_wider_s15, le_s15_target],
    );
    let final_order = d.lemma(
        rat.le_trans,
        &[total, wider, target_bound, order, le_wider_target],
    );

    let result = weaken(d, p, diff, total, target_bound, raw, final_order);

    let ty = {
        let claim = within(d, p, diff, target_bound);
        let after_hle = d.arrow(hle_ty, claim);
        let over_b = d.pi_fv(b_fv, nat, after_hle);
        let over_a = d.pi_fv(a_fv, nat, over_b);
        let with_hk = d.pi_fv(hk_fv, hk_ty, over_a);
        let with_bigk = d.pi_fv(bigk_fv, nat, with_hk);
        let with_h = d.pi_fv(h_fv, h_ty, with_bigk);
        let with_k = d.pi_fv(k_fv, nat, with_h);
        let with_hx0 = d.pi_fv(hx0_fv, hx0_ty, with_k);
        d.pi_fv(x_fv, carrier, with_hx0)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, result);
        let over_b = d.lam_fv(b_fv, nat, with_hle);
        let over_a = d.lam_fv(a_fv, nat, over_b);
        let with_hk = d.lam_fv(hk_fv, hk_ty, over_a);
        let with_bigk = d.lam_fv(bigk_fv, nat, with_hk);
        let with_h = d.lam_fv(h_fv, h_ty, with_bigk);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_k);
        d.lam_fv(x_fv, carrier, with_hx0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_cauchy_of_lt_ordered,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.geomCauchyOfLt`. See the module documentation above
/// [`declare_geom_cauchy_of_lt_ordered`] for the derivation: eliminates
/// `geomYBound`'s outer existential to obtain `(bigK, hK)`, then runs the
/// same `Nat.le_total` case split `exponential.rs::declare_geom_cauchy` runs
/// against `geomCauchyOrderedHalf`, here against
/// [`declare_geom_cauchy_of_lt_ordered`], with witness `geom_cauchy_of_lt_k_final(bigK)`
/// in place of that theorem's fixed `K := 7`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_geom_cauchy_of_lt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hx0_ty = cle(d, p, zero_c, x);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);
    let hlt_ty = d.const_app(p.lt, &[x, one_c]);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);

    let neg_x = cneg(d, p, x);
    let a_real = cadd(d, p, one_c, neg_x);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let h_ty = pos_bound_of(d, p, a_real, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let inv_expr = cinv(d, p, a_real, k, h);

    let f = pow_fn(d, p, x);
    let sum_f = d.const_app(p.sum_range, &[f]);
    let target = d.const_app(p.cauchy, &[sum_f]);

    let ex_yb = d.lemma(p.geom_y_bound, &[x, hx0, hlt, k, h]);

    let predicate1 = {
        let k1_fv = d.fresh_fvar();
        let k1 = d.kernel().fvar(k1_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let pow_xa = d.const_app(p.pow, &[x, a]);
        let mul_iv_pow = cmul(d, p, inv_expr, pow_xa);
        let bound_rat = div_succ_var(d, p, k1, a);
        let bound = embed(d, p, bound_rat);
        let body = cle(d, p, mul_iv_pow, bound);
        let inner = d.pi_fv(a_fv, nat, body);
        d.lam_fv(k1_fv, nat, inner)
    };

    let minor = {
        let bigk_fv = d.fresh_fvar();
        let bigk = d.kernel().fvar(bigk_fv);
        let hk_ty = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let pow_xa = d.const_app(p.pow, &[x, a]);
            let mul_iv_pow = cmul(d, p, inv_expr, pow_xa);
            let bound_rat = div_succ_var(d, p, bigk, a);
            let bound = embed(d, p, bound_rat);
            let body = cle(d, p, mul_iv_pow, bound);
            d.pi_fv(a_fv, nat, body)
        };
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);

        let k_final = geom_cauchy_of_lt_k_final(d, bigk);

        let case_proof = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);

            let sum_f_m = d.const_app(p.sum_range, &[f, m]);
            let sum_f_n = d.const_app(p.sum_range, &[f, n]);
            let y_m = sample(d, p, sum_f_m, m);
            let z_n = sample(d, p, sum_f_n, n);
            let diff_mn = rsub(d, rat, y_m, z_n);
            let bm = div_succ_var(d, p, k_final, m);
            let bn = div_succ_var(d, p, k_final, n);
            let bound_mn = radd(d, bm, bn);
            let claim_mn = within(d, p, diff_mn, bound_mn);

            let left_ty = d.le(m, n);
            let right_ty = d.le(n, m);
            let total_mn = {
                let name = d.prelude().le_total;
                d.const_app(name, &[m, n])
            };

            let body = d.or_elim(
                left_ty,
                right_ty,
                claim_mn,
                total_mn,
                // m <= n: `geom_cauchy_of_lt_ordered` at (a := m, b := n)
                // gives `Within (z_n - y_m) (bn2 + bm2)`; flip the
                // difference, then reorder the bound.
                &|d, hmn| {
                    let raw = d.lemma(
                        p.geom_cauchy_of_lt_ordered,
                        &[x, hx0, k, h, bigk, hk, m, n, hmn],
                    );
                    let bn2 = div_succ_var(d, p, k_final, n);
                    let bm2 = div_succ_var(d, p, k_final, m);
                    let bound_nm = radd(d, bn2, bm2);
                    let flipped = within_symm(d, p, z_n, y_m, bound_nm, raw);
                    let comm_eq = d.lemma(rat.add_comm, &[bn2, bm2]);
                    rat_eq_rewrite(d, bound_nm, bound_mn, comm_eq, flipped, &|d, t| {
                        within(d, p, diff_mn, t)
                    })
                },
                // n <= m: `geom_cauchy_of_lt_ordered` at (a := n, b := m)
                // lands exactly on `Within (y_m - z_n) (bm + bn)` -- no
                // rewrite.
                &|d, hnm| {
                    d.lemma(
                        p.geom_cauchy_of_lt_ordered,
                        &[x, hx0, k, h, bigk, hk, n, m, hnm],
                    )
                },
            );
            let over_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(m_fv, nat, over_n)
        };

        let predicate_f = {
            let kf_fv = d.fresh_fvar();
            let kf = d.kernel().fvar(kf_fv);
            let body = sum_range_cauchy_body(d, p, sum_f, kf);
            d.lam_fv(kf_fv, nat, body)
        };
        let target_proof = exists_nat_intro(d, p, predicate_f, k_final, case_proof);

        let with_hk = d.lam_fv(hk_fv, hk_ty, target_proof);
        d.lam_fv(bigk_fv, nat, with_hk)
    };

    let proof_body = exists_elim(d, predicate1, target, ex_yb, minor);

    let ty = {
        let inner = d.pi_fv(h_fv, h_ty, target);
        let with_k = d.pi_fv(k_fv, nat, inner);
        let after_hlt = d.arrow(hlt_ty, with_k);
        let after_hx0 = d.arrow(hx0_ty, after_hlt);
        d.pi_fv(x_fv, carrier, after_hx0)
    };
    let value = {
        let inner = d.lam_fv(h_fv, h_ty, proof_body);
        let with_k = d.lam_fv(k_fv, nat, inner);
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, with_k);
        let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_hlt);
        d.lam_fv(x_fv, carrier, with_hx0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_cauchy_of_lt,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.natDivSucc k j`, with `k` a **variable** rather than a literal --
/// [`div_succ`] only takes a `u32`, and this file's general-ratio bound needs
/// the modulus at the symbolic witness `bigK`. Verbatim copy of
/// `series.rs::div_succ_var` (private there).
fn div_succ_var(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, j])
}

/// `CReal.geomCauchyOrderedOfGap`. See the field documentation
/// ([`super::CRealPrelude::geom_cauchy_ordered_of_gap`]) for the statement
/// and why it exists.
///
/// Pure composition, no new arithmetic:
/// [`declare_pow_le_nat_div_succ_of_gap`] at `(q, k3)` gives the raw
/// harmonic bound at `k1 := Nat.succ k3`; [`declare_geom_y_bound_raw`] scales
/// it by `inv (1 - x)` to `bigK := (Nat.succ k) * k1`; and that is exactly
/// [`declare_geom_cauchy_of_lt_ordered`]'s own `hK` parameter, which was
/// already raw. The final modulus is
/// [`geom_cauchy_of_lt_k_final`] of that `bigK`, i.e. `((succ k * succ k3) +
/// 1) + 7`, reconstructed here by the same shared Rust function so both sites
/// build the identical `ExprId`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_geom_cauchy_ordered_of_gap(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hx0_ty = cle(d, p, zero_c, x);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let q_emb = embed(d, p, q);
    let x_plus_q = cadd(d, p, x, q_emb);
    let hq_ty = cle(d, p, x_plus_q, one_c);
    let hq_fv = d.fresh_fvar();
    let hq = d.kernel().fvar(hq_fv);

    let k3_fv = d.fresh_fvar();
    let k3 = d.kernel().fvar(k3_fv);
    let hpb_ty = d.const_app(p.pos_bound, &[q_emb, k3]);
    let hpb_fv = d.fresh_fvar();
    let hpb = d.kernel().fvar(hpb_fv);

    let neg_x = cneg(d, p, x);
    let a_real = cadd(d, p, one_c, neg_x);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let h_ty = pos_bound_of(d, p, a_real, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = d.le(a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    // hk1 : ∀ m, le (pow x m) (ofRat (natDivSucc (succ k3) m))
    let hk1 = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let leaf = d.lemma(p.pow_le_nat_div_succ_of_gap, &[x, hx0, q, hq, k3, hpb, m]);
        d.lam_fv(m_fv, nat, leaf)
    };
    let k1 = d.succ(k3);

    // hk : ∀ a, le (mul (inv (1-x) k h) (pow x a)) (ofRat (natDivSucc bigk a))
    let hk = {
        let a0_fv = d.fresh_fvar();
        let a0 = d.kernel().fvar(a0_fv);
        let leaf = d.lemma(p.geom_y_bound_raw, &[x, hx0, k, h, k1, hk1, a0]);
        d.lam_fv(a0_fv, nat, leaf)
    };
    let succ_k = d.succ(k);
    let bigk = NatOps::mul(d, succ_k, k1);

    let result = d.lemma(
        p.geom_cauchy_of_lt_ordered,
        &[x, hx0, k, h, bigk, hk, a, b, hab],
    );

    // Reconstruct `geomCauchyOfLtOrdered`'s own conclusion at `bigk`.
    let f = pow_fn(d, p, x);
    let sum_f_b = d.const_app(p.sum_range, &[f, b]);
    let sum_f_a = d.const_app(p.sum_range, &[f, a]);
    let y_pt = sample(d, p, sum_f_b, b);
    let z_pt = sample(d, p, sum_f_a, a);
    let diff = rsub(d, rat, y_pt, z_pt);
    let k_final = geom_cauchy_of_lt_k_final(d, bigk);
    let nds_b = div_succ_var(d, p, k_final, b);
    let nds_a = div_succ_var(d, p, k_final, a);
    let target_bound = radd(d, nds_b, nds_a);
    let claim = within(d, p, diff, target_bound);

    let ty = {
        let after_hab = d.arrow(hab_ty, claim);
        let over_b = d.pi_fv(b_fv, nat, after_hab);
        let over_a = d.pi_fv(a_fv, nat, over_b);
        let with_h = d.pi_fv(h_fv, h_ty, over_a);
        let with_k = d.pi_fv(k_fv, nat, with_h);
        let with_hpb = d.pi_fv(hpb_fv, hpb_ty, with_k);
        let with_k3 = d.pi_fv(k3_fv, nat, with_hpb);
        let with_hq = d.pi_fv(hq_fv, hq_ty, with_k3);
        let with_q = d.pi_fv(q_fv, rat_carrier, with_hq);
        let with_hx0 = d.pi_fv(hx0_fv, hx0_ty, with_q);
        d.pi_fv(x_fv, carrier, with_hx0)
    };
    let value = {
        let with_hab = d.lam_fv(hab_fv, hab_ty, result);
        let over_b = d.lam_fv(b_fv, nat, with_hab);
        let over_a = d.lam_fv(a_fv, nat, over_b);
        let with_h = d.lam_fv(h_fv, h_ty, over_a);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_hpb = d.lam_fv(hpb_fv, hpb_ty, with_k);
        let with_k3 = d.lam_fv(k3_fv, nat, with_hpb);
        let with_hq = d.lam_fv(hq_fv, hq_ty, with_k3);
        let with_q = d.lam_fv(q_fv, rat_carrier, with_hq);
        let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_q);
        d.lam_fv(x_fv, carrier, with_hx0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_cauchy_ordered_of_gap,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.geomCauchyOrderedOfGap` eta-applied to its OWN binders, closed back
/// up -- the term `creal_tests` checks against that theorem's stored type.
///
/// With `swapped = true` the `hq` and `PosBound (ofRat q) k3` arguments are
/// transposed at the call site and nothing else changes, which the kernel must
/// refuse: those two hypotheses are unrelated Props, and a checker that merely
/// counted positional arguments would accept both.
///
/// Deliberately SYMBOLIC -- every argument is a fresh fvar. The concrete
/// counterpart of this control lives in
/// `creal_tests::the_gap_identity_holds_at_16_over_25_and_fails_at_the_transposed_ratio`,
/// and an earlier version of THIS control that ran at the concrete `16/25`
/// witnesses cost 440 s in a debug build, because a failing defeq on numerals
/// unfolds everything before giving up. Against fvars there is nothing to
/// unfold.
#[cfg(test)]
pub(super) fn geom_cauchy_ordered_of_gap_self_application(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    swapped: bool,
) -> ExprId {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hx0_ty = cle(d, p, zero_c, x);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let q_emb = embed(d, p, q);
    let x_plus_q = cadd(d, p, x, q_emb);
    let hq_ty = cle(d, p, x_plus_q, one_c);
    let hq_fv = d.fresh_fvar();
    let hq = d.kernel().fvar(hq_fv);

    let k3_fv = d.fresh_fvar();
    let k3 = d.kernel().fvar(k3_fv);
    let hpb_ty = d.const_app(p.pos_bound, &[q_emb, k3]);
    let hpb_fv = d.fresh_fvar();
    let hpb = d.kernel().fvar(hpb_fv);

    let neg_x = cneg(d, p, x);
    let a_real = cadd(d, p, one_c, neg_x);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let h_ty = pos_bound_of(d, p, a_real, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = d.le(a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let args = if swapped {
        [x, hx0, q, hpb, k3, hq, k, h, a, b, hab]
    } else {
        [x, hx0, q, hq, k3, hpb, k, h, a, b, hab]
    };
    let applied = d.lemma(p.geom_cauchy_ordered_of_gap, &args);

    let with_hab = d.lam_fv(hab_fv, hab_ty, applied);
    let over_b = d.lam_fv(b_fv, nat, with_hab);
    let over_a = d.lam_fv(a_fv, nat, over_b);
    let with_h = d.lam_fv(h_fv, h_ty, over_a);
    let with_k = d.lam_fv(k_fv, nat, with_h);
    let with_hpb = d.lam_fv(hpb_fv, hpb_ty, with_k);
    let with_k3 = d.lam_fv(k3_fv, nat, with_hpb);
    let with_hq = d.lam_fv(hq_fv, hq_ty, with_k3);
    let with_q = d.lam_fv(q_fv, rat_carrier, with_hq);
    let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_q);
    d.lam_fv(x_fv, carrier, with_hx0)
}

/// `CReal.geomCauchyOrdered16Over25` -- [`declare_geom_cauchy_ordered_of_gap`]
/// instantiated at the concrete ratio `16/25`, i.e. `natDivSucc 16 24`.
///
/// ## Why this ratio and not another
///
/// Spivak's `π := 2·(first zero of cos)` needs `cosFn` past `x = 1`, and
/// `creal/trig_fn.rs`'s module documentation derives the pointwise bound
/// `abs (cosFnTerm k x) ≤ 2·((R/2)²)^k` for `0 ≤ x ≤ R`. So the dominating
/// series is geometric at ratio `(R/2)²`, and the ratio must be large enough
/// that `R` clears cosine's first zero, `≈ 1.5708`:
///
/// * `R := 8/5 = 1.6 > 1.5708`, ratio `(4/5)² = 16/25 = 0.64`. **This one.**
/// * `R := 3/2 = 1.5`, ratio `9/16 = 0.5625` -- named as an example
///   elsewhere, but `1.5 < 1.5708`, so it does **not** clear the zero and
///   does not unblock π.
/// * `R := 7/4 = 1.75`, ratio `49/64 ≈ 0.766` -- also clears it, and is
///   equally reachable by this route (only the three rational obligations
///   below change).
///
/// Note `16/25 > 1/2`, so this is genuinely outside what
/// `CReal.geomCauchyOrderedHalf` and `CRealPrelude::pow_half_le_nat_div_succ`
/// reach: `pow_le_pow_of_base_le` compares upward, not downward, so no
/// amount of base monotonicity gets `(16/25)^k` under `(1/2)^k`.
///
/// ## What the caller owes, and how each obligation is discharged
///
/// The denominator index `24` (denominator `25`) is chosen so that all three
/// rational obligations are single lemma applications at ONE common
/// denominator, with no `Rat` division, no `Rat.normalize`, and no ℕ
/// subtraction:
///
/// * `hq : le (add x (ofRat q)) one` at `q := 9/25` -- because
///   `16/25 + 9/25 = 25/25 = 1`, i.e. `Rat.natDivSucc_add` followed by
///   [`nat_div_succ_succ_self_eq_one`], lifted by
///   [`super::CRealPrelude::of_rat_add`]. It is an `Equiv`, weakened to `le`.
/// * `PosBound (ofRat q) 24` -- `1/25 ≤ 9/25`, one
///   `Rat.natDivSucc_le_add_left` at `(1, 8, 24)`.
/// * `PosBound (add one (neg x)) 24` -- the SAME fact transported across
///   `Equiv (add one (neg x)) (ofRat q)`, which follows from the `hq` `Equiv`
///   by pure group algebra (`add_comm`/`add_assoc`/`add_neg`/`add_zero`), so
///   no rational subtraction and no `of_rat_neg` is needed.
///
/// The resulting modulus is `((25*25) + 1) + 7`, left unreduced.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
/// `CReal.geomCauchyBodyOfGap`. See the field documentation
/// ([`super::CRealPrelude::geom_cauchy_body_of_gap`]) for the statement and
/// why the ORDER-FREE, still-raw form is the one a `Type`-valued consumer
/// actually takes.
///
/// Verbatim in technique to `exponential.rs::declare_geom_cauchy`'s own
/// `Nat.le_total` case split against `geomCauchyOrderedHalf`, here against
/// [`declare_geom_cauchy_ordered_of_gap`] and at the symbolic modulus
/// [`geom_cauchy_of_lt_k_final`] rather than the literal `7` -- and, the one
/// difference that matters, **stopping before that theorem's
/// `Exists.intro`**. `declare_geom_cauchy` wraps this same body into
/// `CReal.Cauchy`, a `Prop` existential, which `Exists.rec` cannot then
/// unwrap into a `Type`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_geom_cauchy_body_of_gap(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hx0_ty = cle(d, p, zero_c, x);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let q_emb = embed(d, p, q);
    let x_plus_q = cadd(d, p, x, q_emb);
    let hq_ty = cle(d, p, x_plus_q, one_c);
    let hq_fv = d.fresh_fvar();
    let hq = d.kernel().fvar(hq_fv);

    let k3_fv = d.fresh_fvar();
    let k3 = d.kernel().fvar(k3_fv);
    let hpb_ty = d.const_app(p.pos_bound, &[q_emb, k3]);
    let hpb_fv = d.fresh_fvar();
    let hpb = d.kernel().fvar(hpb_fv);

    let neg_x = cneg(d, p, x);
    let a_real = cadd(d, p, one_c, neg_x);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let h_ty = pos_bound_of(d, p, a_real, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let f = pow_fn(d, p, x);
    let sum_f = d.const_app(p.sum_range, &[f]);
    let succ_k = d.succ(k);
    let k1 = d.succ(k3);
    let bigk = NatOps::mul(d, succ_k, k1);
    let k_final = geom_cauchy_of_lt_k_final(d, bigk);

    let case_proof = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let sum_f_m = d.const_app(p.sum_range, &[f, m]);
        let sum_f_n = d.const_app(p.sum_range, &[f, n]);
        let y_m = sample(d, p, sum_f_m, m);
        let z_n = sample(d, p, sum_f_n, n);
        let diff_mn = rsub(d, rat, y_m, z_n);
        let bm = div_succ_var(d, p, k_final, m);
        let bn = div_succ_var(d, p, k_final, n);
        let bound_mn = radd(d, bm, bn);
        let claim_mn = within(d, p, diff_mn, bound_mn);

        let left_ty = d.le(m, n);
        let right_ty = d.le(n, m);
        let total_mn = {
            let name = d.prelude().le_total;
            d.const_app(name, &[m, n])
        };

        let body = d.or_elim(
            left_ty,
            right_ty,
            claim_mn,
            total_mn,
            // m <= n: the ordered theorem at (a := m, b := n) gives
            // `Within (z_n - y_m) (bn + bm)`; flip the difference, then
            // reorder the bound.
            &|d, hmn| {
                let raw = d.lemma(
                    p.geom_cauchy_ordered_of_gap,
                    &[x, hx0, q, hq, k3, hpb, k, h, m, n, hmn],
                );
                let bn2 = div_succ_var(d, p, k_final, n);
                let bm2 = div_succ_var(d, p, k_final, m);
                let bound_nm = radd(d, bn2, bm2);
                let flipped = within_symm(d, p, z_n, y_m, bound_nm, raw);
                let comm_eq = d.lemma(rat.add_comm, &[bn2, bm2]);
                rat_eq_rewrite(d, bound_nm, bound_mn, comm_eq, flipped, &|d, t| {
                    within(d, p, diff_mn, t)
                })
            },
            // n <= m: the ordered theorem at (a := n, b := m) lands exactly on
            // `Within (y_m - z_n) (bm + bn)` -- no rewrite.
            &|d, hnm| {
                d.lemma(
                    p.geom_cauchy_ordered_of_gap,
                    &[x, hx0, q, hq, k3, hpb, k, h, n, m, hnm],
                )
            },
        );
        let over_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(m_fv, nat, over_n)
    };

    let claim = sum_range_cauchy_body(d, p, sum_f, k_final);

    let ty = {
        let with_h = d.pi_fv(h_fv, h_ty, claim);
        let with_k = d.pi_fv(k_fv, nat, with_h);
        let with_hpb = d.pi_fv(hpb_fv, hpb_ty, with_k);
        let with_k3 = d.pi_fv(k3_fv, nat, with_hpb);
        let with_hq = d.pi_fv(hq_fv, hq_ty, with_k3);
        let with_q = d.pi_fv(q_fv, rat_carrier, with_hq);
        let with_hx0 = d.pi_fv(hx0_fv, hx0_ty, with_q);
        d.pi_fv(x_fv, carrier, with_hx0)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, h_ty, case_proof);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_hpb = d.lam_fv(hpb_fv, hpb_ty, with_k);
        let with_k3 = d.lam_fv(k3_fv, nat, with_hpb);
        let with_hq = d.lam_fv(hq_fv, hq_ty, with_k3);
        let with_q = d.lam_fv(q_fv, rat_carrier, with_hq);
        let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_q);
        d.lam_fv(x_fv, carrier, with_hx0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_cauchy_body_of_gap,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.geomCauchyBody16Over25` -- [`declare_geom_cauchy_body_of_gap`] at
/// the concrete ratio `16/25`, sharing [`ratio_16_over_25_witnesses`] with
/// [`declare_geom_cauchy_ordered_16_over_25`].
///
/// This is the object `CReal.weierstrassMTest` takes as its `hcauchy`
/// argument at a dominating series of ratio `16/25`, and the first such
/// object in this kernel at any ratio other than `1/2`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_geom_cauchy_body_16_over_25(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let (x, hx0, q_rat, hq, n24, hpb_q, h) = ratio_16_over_25_witnesses(d, p);
    let value = d.lemma(
        p.geom_cauchy_body_of_gap,
        &[x, hx0, q_rat, hq, n24, hpb_q, n24, h],
    );

    let f = pow_fn(d, p, x);
    let sum_f = d.const_app(p.sum_range, &[f]);
    let succ24 = d.succ(n24);
    let bigk = NatOps::mul(d, succ24, succ24);
    let k_final = geom_cauchy_of_lt_k_final(d, bigk);
    let ty = sum_range_cauchy_body(d, p, sum_f, k_final);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_cauchy_body_16_over_25,
        uparams: vec![],
        ty,
        value,
    })
}

/// The three rational obligations `CReal.geomCauchyOrderedOfGap` needs at
/// the ratio `16/25`, as `(x, hx0, q_rat, hq, k3 = 24, hpb_q, h)`.
///
/// Split out of [`declare_geom_cauchy_ordered_16_over_25`] so that a second
/// ratio (`49/64` at `R := 7/4`, say) is a copy of THIS function with three
/// numerals changed and nothing else, rather than a copy of the whole
/// declaration.
#[allow(clippy::type_complexity)]
pub(super) fn ratio_16_over_25_witnesses(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let one_c = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);
    let zero_r = rzero(d, rat);
    let one_r = rone(d, rat);

    let n1 = d.num(1);
    let n8 = d.num(8);
    let n9 = d.num(9);
    let n16 = d.num(16);
    let n24 = d.num(24);

    let x_rat = d.const_app(rat.nat_div_succ, &[n16, n24]);
    let x = embed(d, p, x_rat);
    let q_rat = d.const_app(rat.nat_div_succ, &[n9, n24]);
    let q_emb = embed(d, p, q_rat);

    // hx0 : le zero x
    let hx0 = {
        let nn = d.lemma(rat.zero_le_nat_div_succ, &[n16, n24]);
        d.lemma(p.of_rat_le, &[zero_r, x_rat, nn])
    };

    // h_sum_rat : Eq (16/25 + 9/25) 1, via `natDivSucc_add` then
    // `natDivSucc (succ 24) 24 = 1`. `Nat.add 16 9` and `Nat.succ 24` are the
    // same unary numeral, so no bridge lemma is needed between them.
    let sum_rat = radd(d, x_rat, q_rat);
    let add_eq = d.lemma(rat.nat_div_succ_add, &[n16, n9, n24]);
    let succ24 = d.succ(n24);
    let mid_rat = d.const_app(rat.nat_div_succ, &[succ24, n24]);
    let self_one = nat_div_succ_succ_self_eq_one(d, p, n24);
    let h_sum_rat = rtrans(d, sum_rat, mid_rat, one_r, add_eq, self_one);

    // h_sum : Equiv (add x (ofRat q)) one
    let x_plus_q = cadd(d, p, x, q_emb);
    let of_add = d.lemma(p.of_rat_add, &[x_rat, q_rat]);
    let sum_equiv_one = embed_eq_to_equiv(d, p, sum_rat, one_r, h_sum_rat);
    let embed_sum = embed(d, p, sum_rat);
    let h_sum = d.lemma(
        p.equiv_trans,
        &[x_plus_q, embed_sum, one_c, of_add, sum_equiv_one],
    );

    // hq : le (add x (ofRat q)) one -- `le_refl one` moved across `h_sum`.
    let hq = {
        let h_sum_symm = d.lemma(p.equiv_symm, &[x_plus_q, one_c, h_sum]);
        let refl_one = d.lemma(p.equiv_refl, &[one_c]);
        let le_one_one = d.lemma(p.le_refl, &[one_c]);
        d.lemma(
            p.le_congr,
            &[
                one_c, x_plus_q, one_c, one_c, h_sum_symm, refl_one, le_one_one,
            ],
        )
    };

    // hpb_q : PosBound (ofRat q) 24, i.e. `le (ofRat (1/25)) (ofRat (9/25))`.
    let small_rat = d.const_app(rat.nat_div_succ, &[n1, n24]);
    let hpb_q = {
        let raw = d.lemma(rat.nat_div_succ_le_add_left, &[n1, n8, n24]);
        d.lemma(p.of_rat_le, &[small_rat, q_rat, raw])
    };

    // h_gap : Equiv (add one (neg x)) (ofRat q) -- pure group algebra from
    // `h_sum`, so nothing here needs `Rat` subtraction or `of_rat_neg`.
    let neg_x = cneg(d, p, x);
    let one_minus_x = cadd(d, p, one_c, neg_x);
    let h_gap = {
        let refl_negx = d.lemma(p.equiv_refl, &[neg_x]);
        let h_sum_symm = d.lemma(p.equiv_symm, &[x_plus_q, one_c, h_sum]);
        // step1 : Equiv (add one (neg x)) (add (add x q) (neg x))
        let xq_negx = cadd(d, p, x_plus_q, neg_x);
        let step1 = d.lemma(
            p.add_congr,
            &[one_c, x_plus_q, neg_x, neg_x, h_sum_symm, refl_negx],
        );
        // step2 : Equiv (add (add x q) (neg x)) (add (add q x) (neg x))
        let comm_xq = d.lemma(p.add_comm, &[x, q_emb]);
        let q_plus_x = cadd(d, p, q_emb, x);
        let refl_negx2 = d.lemma(p.equiv_refl, &[neg_x]);
        let step2 = d.lemma(
            p.add_congr,
            &[x_plus_q, q_plus_x, neg_x, neg_x, comm_xq, refl_negx2],
        );
        let qx_negx = cadd(d, p, q_plus_x, neg_x);
        // step3 : Equiv (add (add q x) (neg x)) (add q (add x (neg x)))
        let step3 = d.lemma(p.add_assoc, &[q_emb, x, neg_x]);
        let x_negx = cadd(d, p, x, neg_x);
        let q_x_negx = cadd(d, p, q_emb, x_negx);
        // step4 : Equiv (add q (add x (neg x))) (add q zero)
        let refl_q = d.lemma(p.equiv_refl, &[q_emb]);
        let addneg = d.lemma(p.add_neg, &[x]);
        let step4 = d.lemma(p.add_congr, &[q_emb, q_emb, x_negx, zero_c, refl_q, addneg]);
        let q_plus_zero = cadd(d, p, q_emb, zero_c);
        // step5 : Equiv (add q zero) q
        let step5 = d.lemma(p.add_zero, &[q_emb]);

        let c1 = d.lemma(
            p.equiv_trans,
            &[one_minus_x, xq_negx, qx_negx, step1, step2],
        );
        let c2 = d.lemma(p.equiv_trans, &[one_minus_x, qx_negx, q_x_negx, c1, step3]);
        let c3 = d.lemma(
            p.equiv_trans,
            &[one_minus_x, q_x_negx, q_plus_zero, c2, step4],
        );
        d.lemma(p.equiv_trans, &[one_minus_x, q_plus_zero, q_emb, c3, step5])
    };

    // h : PosBound (add one (neg x)) 24
    let h = {
        let small_emb = embed(d, p, small_rat);
        let refl_small = d.lemma(p.equiv_refl, &[small_emb]);
        let gap_symm = d.lemma(p.equiv_symm, &[one_minus_x, q_emb, h_gap]);
        d.lemma(
            p.le_congr,
            &[
                small_emb,
                small_emb,
                q_emb,
                one_minus_x,
                refl_small,
                gap_symm,
                hpb_q,
            ],
        )
    };

    (x, hx0, q_rat, hq, n24, hpb_q, h)
}

/// `CReal.geomCauchyOrdered16Over25`. See the note above
/// [`ratio_16_over_25_witnesses`] and the field documentation
/// ([`super::CRealPrelude::geom_cauchy_ordered_16_over_25`]).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_geom_cauchy_ordered_16_over_25(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let (x, hx0, q_rat, hq, n24, hpb_q, h) = ratio_16_over_25_witnesses(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = d.le(a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let result = d.lemma(
        p.geom_cauchy_ordered_of_gap,
        &[x, hx0, q_rat, hq, n24, hpb_q, n24, h, a, b, hab],
    );

    // Restate the conclusion at the concrete moduli, matching
    // `declare_geom_cauchy_ordered_of_gap`'s own construction exactly.
    let f = pow_fn(d, p, x);
    let sum_f_b = d.const_app(p.sum_range, &[f, b]);
    let sum_f_a = d.const_app(p.sum_range, &[f, a]);
    let y_pt = sample(d, p, sum_f_b, b);
    let z_pt = sample(d, p, sum_f_a, a);
    let diff = rsub(d, rat, y_pt, z_pt);
    let succ24b = d.succ(n24);
    let bigk = NatOps::mul(d, succ24b, succ24b);
    let k_final = geom_cauchy_of_lt_k_final(d, bigk);
    let nds_b = div_succ_var(d, p, k_final, b);
    let nds_a = div_succ_var(d, p, k_final, a);
    let target_bound = radd(d, nds_b, nds_a);
    let claim = within(d, p, diff, target_bound);

    let ty = {
        let after_hab = d.arrow(hab_ty, claim);
        let over_b = d.pi_fv(b_fv, nat, after_hab);
        d.pi_fv(a_fv, nat, over_b)
    };
    let value = {
        let with_hab = d.lam_fv(hab_fv, hab_ty, result);
        let over_b = d.lam_fv(b_fv, nat, with_hab);
        d.lam_fv(a_fv, nat, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_cauchy_ordered_16_over_25,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.geomCauchyOfLtOrdered` and `CReal.geomCauchyOfLt`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_geom_cauchy_of_lt_family(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_geom_cauchy_of_lt_ordered(d, p)?;
    declare_geom_cauchy_of_lt(d, p)?;
    declare_geom_cauchy_ordered_of_gap(d, p)?;
    declare_geom_cauchy_body_of_gap(d, p)?;
    declare_geom_cauchy_ordered_16_over_25(d, p)?;
    declare_geom_cauchy_body_16_over_25(d, p)
}
