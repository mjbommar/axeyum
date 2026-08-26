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
//! **This is not yet `Cauchy`, and landing it does not finish the goal.**
//! Reaching `Cauchy`'s own `∃ K, ∀ m n, Within (…) (natDivSucc K m +
//! natDivSucc K n)` shape from `geom_tail_within` needs bounding the deferred
//! sample `seq Yₘ (add m n)` — a quantity that decays **geometrically** in
//! `m` — by a **harmonic**-shaped `natDivSucc K' m` for one `K'` fixed
//! *uniformly in `m`*. That is not index arithmetic; it is a genuine missing
//! piece of real analysis, and nothing in this development supplies it:
//! there is no lemma bounding `CReal.pow` above by a `natDivSucc` rational, no
//! lemma comparing `pow` at two different bases for the same exponent
//! (needed to compare `xⁿ` against `(1−ε)ⁿ` for the rational `ε` `PosBound`
//! supplies), and no Bernoulli-type inequality (`(1+ε)ⁿ ≥ 1+nε`) from which
//! such a bound is normally derived. Each is a standalone, moderate
//! induction in its own right (see this file's own `geom_tail_nonneg` for
//! the size of a *comparable* induction), but together they are substantially
//! more work than the index-arithmetic difficulty this task was framed
//! around, and none of the three exists yet in any file this slice may
//! touch. **This is the precise remaining blocker for `CReal.geom_cauchy`.**
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

use super::{CRealPrelude, and_intro, creal_ty, div_succ, halves, modulus, sample, shift, within};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{nat_rewrite_prop, radd, rat_eq_rewrite, rle, rneg};

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
    declare_pow_le_pow_of_base_le(d, p)
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
