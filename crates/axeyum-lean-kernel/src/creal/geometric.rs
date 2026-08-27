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

use super::series::exists_nat_intro;
use super::{
    CRealPrelude, and_intro, creal_ty, div_succ, embed, equiv, gap_elim, gap_halves, halves,
    modulus, sample, shift, within,
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

/// `Equiv (neg zero) zero`. Verbatim copy of `series.rs::neg_zero_equiv`
/// (private there): the group identity `−0 = 0`, from
/// [`CRealPrelude::add_zero`]/[`CRealPrelude::add_comm`]/
/// [`CRealPrelude::add_neg`] rather than any `Rat`-level fact.
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]); // padded ~ nz
    let step1 = d.lemma(p.equiv_symm, &[padded, nz, h1]); // nz ~ padded
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]); // padded ~ flipped
    let h3 = d.lemma(p.add_neg, &[zero_c]); // flipped ~ zero
    echain(d, p, nz, &[(padded, step1), (flipped, h2), (zero_c, h3)])
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
    declare_pow_le_nat_div_succ_of_lt(d, p)
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
fn nat_div_succ_succ_self_eq_one(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
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
    let zero_nat = d.num(0);
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

            // ht : le zero_c q_emb
            let ht = {
                let zero_r2 = rzero(d, rat);
                let hqpos_le = d.lemma(rat.le_of_lt, &[zero_r2, q, hqpos]);
                d.lemma(p.of_rat_le, &[zero_r2, q, hqpos_le])
            };

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
                        let unit_to_one =
                            rcongr(d, unit_rat, one_r, unit_eq_one, &|d, t| radd(d, k3_rat, t));
                        let sum_one_to_unit = rsymm(d, sum_unit, sum_one, unit_to_one);
                        let sum_one_to_k =
                            rtrans(d, sum_one, sum_unit, k_rat, sum_one_to_unit, sum_add);
                        let k3_rat_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[k3, zero_nat]);
                        let refl_one_r = d.lemma(rat.le_refl, &[one_r]);
                        let zero_r3 = rzero(d, rat);
                        let sum_le = d.lemma(
                            rat.add_le_add,
                            &[zero_r3, k3_rat, one_r, one_r, k3_rat_nonneg, refl_one_r],
                        );
                        let zero_plus_one = radd(d, zero_r3, one_r);
                        let zero_add_eq = d.lemma(rat.zero_add, &[one_r]);
                        let sum_le_at_one = rat_eq_rewrite(
                            d,
                            zero_plus_one,
                            one_r,
                            zero_add_eq,
                            sum_le,
                            &|d, t| rle(d, rat, t, sum_one),
                        );
                        let rone_le_k_rat = rat_eq_rewrite(
                            d,
                            sum_one,
                            k_rat,
                            sum_one_to_k,
                            sum_le_at_one,
                            &|d, t| rle(d, rat, one_r, t),
                        );
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
                        let idx_step =
                            nat_eq_to_rat(d, big_k_mul_one, big_k, mul_one_nat_h, &|d, kk| {
                                d.const_app(rat.nat_div_succ, &[kk, k3])
                            });
                        let x0 = nat_div_succ_succ_self_eq_one(d, p, k3);
                        let prod_to_mid2 =
                            rtrans(d, prod_rat, mid_rat, mid2_rat, scale_eq, idx_step);
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
                        let congr_xz =
                            d.lemma(p.add_congr, &[x, x, q_plus_negq, zero_c, refl_x, add_neg_h]);
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
                            let e1_symm =
                                d.lemma(p.equiv_symm, &[zero_plus_negzero, neg_zero_c, e1]);
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
                            let raw =
                                mul_le_mul_of_nonneg_right(d, p, x, one_c, q_emb, ht, hx_le_one);
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
                        let congr_x =
                            d.lemma(p.add_congr, &[x_one_c, x, xq, xq, mul_one_x, refl_xq2]);
                        let x_plus_xq = cadd(d, p, x, xq);
                        let x_one_c_plus_xq = cadd(d, p, x_one_c, xq);
                        let dist2 = d.lemma(
                            p.equiv_trans,
                            &[x_one_plus_t, x_one_c_plus_xq, x_plus_xq, dist, congr_x],
                        );

                        let le_refl_xq = d.lemma(p.le_refl, &[xq]);
                        let bound1 =
                            d.lemma(p.add_le_add, &[x, one_minus_q, xq, xq, hr_le, le_refl_xq]);
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
                    let m_fv = d.fresh_fvar();
                    let m = d.kernel().fvar(m_fv);

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
                    let step_ar =
                        mul_le_mul_of_nonneg_right(d, p, a_m, k_lm, pow_xm, pow_nonneg_m, kr_m);
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
                        let idx_step2 =
                            nat_eq_to_rat(d, succ_m_mul_one, succ_m, mul_one_h2, &|d, kk| {
                                d.const_app(rat.nat_div_succ, &[kk, m])
                            });
                        let x0b = nat_div_succ_succ_self_eq_one(d, p, m);
                        let prod_to_mid2b =
                            rtrans(d, prod2, mid_rat2, mid2_rat2, scale_eq2, idx_step2);
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
                    let idx_step3 =
                        nat_eq_to_rat(d, big_k_mul_one2, big_k, mul_one_h3, &|d, kk| {
                            d.const_app(rat.nat_div_succ, &[kk, m])
                        });
                    let kdd_rat = rmul(d, k_rat, dd_rat);
                    let comm_dk = d.lemma(rat.mul_comm, &[dd_rat, k_rat]); // Eq final_rat kdd_rat
                    let kdd_to_mid = rtrans(d, kdd_rat, mid_rat3, mid2_rat3, scale_eq3, idx_step3);
                    let final_to_kdd = comm_dk;
                    let final_to_mid2 =
                        rtrans(d, final_rat, kdd_rat, mid2_rat3, final_to_kdd, kdd_to_mid);
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
                    let per_m_proof = d.lemma(
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
                    );
                    // per_m_proof : le pow_xm (embed (natDivSucc big_k m))

                    let per_m = d.lam_fv(m_fv, nat, per_m_proof);
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
