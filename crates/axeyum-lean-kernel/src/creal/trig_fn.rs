//! **`CReal.cosFn : CReal → CReal`** — general cosine as a genuine function,
//! on the bounded domain `[0, 1]`, via the power series `Σ (-1)^k x^{2k} /
//! (2k)!`. This is the piece `creal/trig.rs`'s own module documentation
//! named as out of scope for `CReal.cosOne` (a single constant, `cos 1`):
//! the general function needed a bound depending on `|x|`, i.e. a power
//! series argument, which `creal/uniform_convergence.rs`'s
//! `weierstrassMTest`/`powerSeriesUniformConvergesOn` now supply.
//!
//! ## Route
//!
//! `CReal.cosFnTerm k x := mul (cosTerm k) (pow x (Nat.add k k))` — the same
//! `cosTerm` `creal/trig.rs::declare_cos_term` already built for `cosOne`,
//! now multiplied by `x^{2k}` instead of implicitly evaluated at `x := 1`.
//! Domain `[0, 1]` is deliberately the CHEAPEST choice available: for `0 ≤ x
//! ≤ 1`, `pow x (Nat.add k k) ≤ one` ([`CRealPrelude::pow_le_one`]) directly,
//! so the domination bound needs **no new domination series at all** — it is
//! `cosTermAbsLeDominant` (`creal/trig.rs`) composed with one
//! `abs_mul_le_of_bounds` step, exactly the sentence the task brief predicted.
//!
//! `CReal.weierstrassMTest` is applied directly (not through
//! `powerSeriesUniformConvergesOn`, whose own coefficient family sums over
//! *every* `Nat` index against `pow x j` — cosine's term is supported only on
//! even exponents, so it needs its own `f`, not a coefficient sequence fed to
//! `powerSeriesTerm`) at `f := cosFnTerm`, `mseq := expDominant`, `a :=
//! zero`, `b := one`. The M-test's own `(k, hcauchy)` parameter pair —
//! required as a **raw**, non-existential Cauchy witness, mirroring
//! `powerSeriesUniformConvergesOn`'s own contract exactly, per this task's
//! brief — is supplied by `exp_dominant_cauchy_body_concrete`
//! (`creal/trig.rs`, marked `pub(super)` for this file), the SAME concrete
//! witness `cosOne`'s own construction already uses for
//! `Cauchy (sumRange expDominant)`. No bridge is needed: that function's
//! return type is already `sum_range_cauchy_body(sumRange expDominant, k)`,
//! which is *exactly* `weierstrassMTest`'s `hcauchy` shape at `mseq :=
//! expDominant`.
//!
//! ## `CReal.cosFn`, and how it is obtained
//!
//! `UniformConvergesOn F G a b`'s own `G : CReal → CReal` is one of that
//! `Type`'s four PARAMETERS (see `creal/uniform_convergence.rs`'s module
//! documentation), built entirely INSIDE `weierstrassMTest`'s own proof from
//! its `f`/`mseq`/`a`/`b`/`hab`/`k`/`hdom`/`hcauchy` arguments — so applying
//! `weierstrassMTest` at cosine's concrete arguments and reading off
//! `Kernel::infer` of the result gives back a CLOSED term for `G`
//! specialized to cosine, without this file re-deriving any of that
//! construction's `pt_clamped`/`case_proof`/`speedup`/`CReal.mk` machinery by
//! hand. [`declare_cos_fn`] does exactly that: build the applied term, infer
//! its type (`UniformConvergesOn F G zero one`), decompose that application
//! spine with [`crate::expr::ExprNode::App`] to extract `G`, and declare
//! `CReal.cosFn := G` as its own `Definition`. `CReal.cosFnUniformConverges`
//! is then declared with the SAME applied term as its `value`, ascribed
//! against a `ty` that names `CReal.cosFn` (rather than `G` again) — the
//! kernel accepts it by δ-unfolding the freshly declared `cosFn` back to `G`,
//! exactly the way `CReal.powerSeriesTerm_abs_le` ascribes its conclusion
//! through the named `CReal.powerSeriesTerm` while its own proof works with
//! the raw `mul`/`pow` term underneath.
//!
//! ## What is NOT built here
//!
//! - **`cosFn 1 ≡ cosOne`.** This needs turning `cosFn`'s own
//!   `UniformConvergesOn`/`close_within` evidence at `x := one` into a raw
//!   `Converges` witness comparable (via `CReal.converges_unique`) against
//!   `cosOneConverges`. That bridge — `close_within` back to the sample-level
//!   `Within` `Converges` needs — does not exist as a public lemma today:
//!   `converges_of_scaled_cauchy`'s own version of this step is buried inside
//!   that theorem's private proof, and the one PUBLIC lemma of this shape,
//!   `within_of_two_sided_le`, runs the *opposite* direction (`Within` to
//!   `close_within`, the direction [`super::uniform_convergence`]'s own
//!   `close_within_of_within` already needed). Building it is a real,
//!   separately-sized proof, not attempted in this file — see this module's
//!   own status note for the exact shape needed.
//! - **`sinFn`**, by the identical route with `sinTerm` — mechanically
//!   parallel to `cosFn` once `cosFn` itself was the open question; not
//!   attempted in the time this slice had.
//! - **Any approximate root of `cosFn`.** Nothing here changes `creal/ivt.rs`'s
//!   refutation of exact-root construction; an *approximate* π via
//!   `ivt_approx`/`ivt_bisect` would additionally need `cosFn`'s own
//!   uniform continuity (from `uniform_limit_uniformly_continuous`, which
//!   itself needs each partial sum `UniformlyContinuousOn` on `[0,1]` — a
//!   finite-sum induction over already-public `uniformly_continuous_add`/
//!   `_mul`/`_const`/`_id`, not attempted here) and a sign change witness,
//!   neither built in this slice.
//!
//! ## Investigated for π (Spivak ch. 15): extending the domain past `[0, 1]`
//! is blocked on a MISSING concrete Cauchy witness, not a missing domain
//! bound
//!
//! Spivak defines `π := 2 · (first zero of cos)`, needing `cosFn` (or at
//! least one point value) evaluated somewhere past `1` — cosine's first
//! zero is `≈ 1.5708`, outside `[0, 1]`. This was investigated in full
//! (domain extension, a numeric sign-change fact, and what `creal/ivt.rs`
//! would hand back) and **nothing here changes the domain**, because the
//! actual obstacle is one level deeper than "no dominating series exists
//! past `x = 1`" — a dominating series is easy to write down; the CONCRETE,
//! non-existential Cauchy witness for it is not, and every route to a real
//! number past `x = 1` needs exactly that.
//!
//! **The pointwise bound itself is cheap and needs no new lemma beyond
//! ones already public.** For `0 ≤ x ≤ R` (any `R`), `abs (cosFnTerm k x) =
//! abs (cosTerm k) · pow x (Nat.add k k) ≤ (mul two (pow half (Nat.add k
//! k))) · pow R (Nat.add k k)` via `exp_term_abs_le_dominant` at index
//! `Nat.add k k` (giving `abs (cosTerm k) ≤ expDominant (Nat.add k k) = 2 ·
//! (1/2)^{2k}` — the TIGHTER, pre-collapse bound `cosTermAbsLeDominant`
//! itself uses internally before its own final `exp_dominant_double_le`
//! step down to `expDominant k`) and [`CRealPrelude::pow_le_pow_of_base_le`]
//! (base monotonicity for `pow`, ALREADY public and general in the base —
//! `geometric.rs`'s own module documentation once named this comparison
//! missing; it no longer is). Multiplying out: `2 · (1/2)^{2k} · R^{2k} = 2
//! · (R/2)^{2k} = 2 · ((R/2)²)^k` — a plain geometric bound with ratio
//! `(R/2)²`, **strictly `< 1` for any `R < 2`**, comfortably including
//! values past `π/2` (e.g. `R := 7/4` gives ratio `49/64`). So domain `[0,
//! R]` for any fixed rational `R < 2` is the right target, not `[0, 2]`
//! itself (ratio exactly `1` at `R = 2`, the M-test's `geom_scaled_cauchy_of_lt`-
//! style route needs it strict) — a smaller correction to this file's own
//! earlier framing, not a new obstacle.
//!
//! **The obstacle is that `CReal.weierstrassMTest`'s `hcauchy` parameter —
//! and, identically, `CReal.mk`'s own regularity argument for building ANY
//! new `CReal` VALUE directly — needs a RAW, non-existential `(k : Nat,
//! proof)` pair, never the `Prop`-wrapped `∃ K, …` `CReal.Cauchy` most
//! convergence machinery in this codebase produces.** `UniformConvergesOn`
//! (`creal/uniform_convergence.rs`) is `Type`-valued exactly so its `G`
//! field can be *computed* from the witness; `Exists.rec`'s motive must not
//! depend on the witness when the target is a `Type`, so a `Cauchy`
//! `Prop`-existential cannot be unwrapped into either `UniformConvergesOn`'s
//! `G` or a fresh `CReal.mk`'s own `Nat → Rat` sequence — the SAME wall
//! `super::exponential`'s own module documentation names for why `CReal.e`
//! needed a "concrete (non-existential) witness" section at all, and why
//! `cosOne` reuses that exact witness rather than deriving its own: at `x =
//! 1`, `pow x (Nat.add k k) ≡ one`, so no NEW ratio is needed, and the
//! existing raw witness for `expDominant` (ratio `1/2`) suffices unchanged.
//! Any `R ≠ 1` needs a genuinely different ratio (`(R/2)²` above), so this
//! shortcut is unavailable for both a domain-extended `cosFn` AND a lone
//! new point value `cos R` — they hit the identical wall.
//!
//! **Confirmed (`shape_search --include-constructed`, positive controls
//! passing) that no shortcut around this exists today:** no `CReal.pi`, no
//! `cos_add`/angle-addition formula (which would let `cos 2` be computed
//! algebraically from `cosOne` without any new series at all), and no
//! `CReal` "power distributes over a product" identity. Exactly one raw,
//! non-existential geometric ordered-half `Within` witness exists in the
//! whole kernel: `CReal.geomCauchyOrderedHalf`, tied to the literal ratio
//! `1/2` via `CReal.geomHalfInvLeafBound`'s `inv`-cancellation at that one
//! concrete value.
//!
//! **What DOES already generalize, confirmed by reading (not just
//! grepping) `creal/geometric.rs` and `creal/exponential.rs`:** the
//! *scaling* combinators that turn a raw ordered-half witness for a base
//! series into one for a constant multiple of it — `exponential.rs`'s
//! private `mul_deshift`, `mul_ordered_half_body`, and
//! `promote_ordered_half_to_full` — already take the base series' own
//! ordered-half proof as a `&dyn Fn` PARAMETER, not a hardcoded fact; they
//! are not the blocker. The blocker is one level further in:
//! `CReal.geomCauchyOfLtOrdered`/`CReal.geomYBound`/
//! `CReal.pow_le_natDivSucc_of_lt` (`geometric.rs`) already generalize the
//! *statement* "geometric decay at ratio `x` dominates some harmonic rate"
//! to an arbitrary `0 ≤ x < 1` — but every one of them is built, and stays,
//! `Prop`-`Exists`-wrapped all the way down (`geom_y_bound`'s own witness
//! `K` is produced by an internal `PosBound`/Bernoulli-harmonic argument
//! that is never factored out as a *raw* pair the way
//! `exp_dominant_cauchy_body_concrete` factors expDominant's). So the
//! generic-ratio machinery answers "does a rate exist" (a `Prop`), never
//! "here is one" (data) — exactly backwards from what a `Type`-valued
//! consumer needs.
//!
//! **What landing this would take, precisely sized for whoever picks it up
//! next:** redo `geometric.rs`'s `declare_pow_le_nat_div_succ_of_lt` →
//! `declare_geom_y_bound` → `geom_half_inv_leaf_bound`-equivalent →
//! `geom_cauchy_ordered_half`-equivalent chain (~150–300 new lines, the
//! same order of magnitude as that chain's own current size) EXPLICITLY —
//! i.e. with every `Exists.intro`/`exists_elim` in that chain replaced by
//! literal `(k, proof)` construction — for ONE chosen literal ratio (e.g.
//! `R := 7/4`, combined ratio `49/64`), rather than symbolically for
//! arbitrary `x` (the existing theorems already cover the symbolic
//! *statement*; only the *witness* needs to stop being existential). The
//! already-generic `mul_deshift`/`mul_ordered_half_body`/
//! `promote_ordered_half_to_full` combinators finish the job unchanged once
//! that one raw ordered-half fact exists. This is a real, separately-sized
//! piece of new arithmetic, not attempted in this slice.
//!
//! **Rung 3, checked ahead of time so the shape of a landed π is not a
//! surprise later:** `CReal.ivt_approx` (`creal/ivt.rs`) is `∀ F a b,
//! UniformlyContinuousOn F a b → le a b → le (F a) zero → le zero (F b) →
//! ∀ e : Nat, ∃ x, le a x ∧ le x b ∧ le (abs (F x)) (ofRat (natDivSucc 1
//! e))` — an APPROXIMATE root family, never `F c ≡ zero`, by the file's own
//! module documentation ("no algorithm produces \[a computable root\] in
//! general"). It also needs `F`'s `UniformlyContinuousOn` (itself
//! `Type`-valued, same reason as `UniformConvergesOn` above, and not built
//! for `cosFn` — see the bullet above), which the raw-witness fix above
//! does not supply. So even with the domain extended, `π` built this way
//! is NOT a single theorem: it is at best a graded family per ADR-0603 —
//! the general `∀ e, ∃ x, …` approximation fact, PLUS a separate,
//! currently-unbuilt argument (likely leaning on `cosFn`'s monotonicity
//! near its zero) that the family of approximate roots itself converges to
//! an actual `CReal`, which `ivt_approx` does not provide for free.
//!
//! ## 2026-08-27 update: the raw-witness wall above is GONE, and two of the
//! three pieces past it are landed -- `weierstrassMTest` is NOT yet applied
//! past `[0, 1]`
//!
//! `creal/geometric.rs` now carries a fully general RAW (non-existential)
//! geometric Cauchy-body family (`CReal.geomCauchyBodyOfGap` and its
//! ratio-`16/25` instance `CReal.geomCauchyOrdered16Over25` /
//! `CReal.geomCauchyBody16Over25`) -- exactly the missing piece this
//! section used to say would cost "~150-300 new lines". `R := 8/5 = 1.6`
//! clears cosine's first zero (`≈ 1.5708`); its dominating ratio is
//! `(R/2)² = 16/25`.
//!
//! **Landed in this slice, both confirmed by the kernel:**
//!
//! 1. [`declare_cos_fn_term_abs_le_wide`] (`CReal.cosFnTermAbsLeWide`) — the
//!    pointwise domination bound for `0 ≤ x ≤ R`, ANY `R`, via
//!    [`CRealPrelude::exp_term_abs_le_dominant`] at the doubled index
//!    (through [`cos_term_abs_le_dom_double`], the pre-collapse bound
//!    `cosTermAbsLeDominant`'s own proof computes internally, extracted
//!    here rather than rebuilt) plus
//!    [`CRealPrelude::pow_le_pow_of_base_le`] — exactly as the task brief
//!    predicted, no new domination series. Its conclusion is `mul
//!    (expDominant (Nat.add k k)) (pow R (Nat.add k k))`, deliberately
//!    UNREDUCED (see point 3 below for why).
//! 2. [`declare_cos_dominant_16_over_25`] / [`declare_cos_dominant_16_over_25_cauchy_body`]
//!    (`CReal.cosDominant16Over25`, `:= fun k => mul two (pow (16/25) k)`,
//!    and its raw Cauchy-body witness) — the "constant-2 scaling" piece the
//!    brief named. [`exponential.rs`]'s/[`trig.rs`]'s own private
//!    `mul_deshift`/`mul_ordered_half_body`/`promote_ordered_half_to_full`/
//!    `cauchy_body_transport` (already generic in the base series' own
//!    ordered-half proof, taken as a `&dyn Fn` parameter) finish this
//!    UNCHANGED once widened to `pub(super)` — **confirmed exactly as
//!    predicted**, no restructuring, only visibility (`trig.rs`'s copies
//!    were widened rather than `exponential.rs`'s: they are byte-identical
//!    reproductions — confirmed by diff — and `trig.rs` already wires the
//!    ratio-`1/2` analogue, `exp_dominant_cauchy_body_concrete`, through
//!    the identical route this file already imports).
//!
//! **NOT landed, and this is a real gap the brief's own framing did not
//! fully anticipate:** `weierstrassMTest` needs its `hdom` hypothesis
//! (`∀ j pt, …, le (abs (f j pt)) (mseq j)`) and `hcauchy` hypothesis (a
//! raw Cauchy body for `sumRange mseq`) to name the SAME `mseq`. Point 1's
//! bound and point 2's dominating series are both real and both raw, but
//! they are NOT (yet) the same term: point 1 gives `mul (expDominant
//! (Nat.add k k)) (pow R (Nat.add k k))`; point 2 gives `mul two (pow
//! (16/25) k)`. Bridging them needs `pow a n * pow b n ≈ pow (mul a b) n`
//! ("power distributes over a product of bases at a fixed exponent") PLUS a
//! rational-arithmetic identity `(1/2 · 8/5)² = 16/25` in the style of
//! `geometric.rs::ratio_16_over_25_witnesses`'s own careful `natDivSucc`
//! bookkeeping. **Neither exists in this kernel today** — confirmed absent
//! from the `pow_*` `CRealPrelude` field list, the same "no power
//! distributes over a product" gap this file's own earlier
//! ("Investigated for π") section already found for a DIFFERENT purpose
//! and did not realize would resurface here. Both are buildable (the first
//! by a short `Nat` induction, mirroring `power.rs::declare_pow_add`'s own
//! proof shape; the second by more `ratio_16_over_25_witnesses`-style
//! rational bookkeeping) but are genuinely NEW arithmetic, not the
//! "unchanged, just widened" piece the brief predicted for step 2 — so
//! `weierstrassMTest` is NOT applied past `[0, 1]` in this slice, and no
//! `cosFnWide` exists yet. `cosFn` itself (`[0, 1]`) is untouched.

use super::geometric::ratio_16_over_25_witnesses;
use super::series::sum_range_cauchy_body;
use super::trig::{
    cabs, cadd, cauchy_body_transport, cle, cmul, cneg, cpow, czero, echain, erefl,
    exp_dominant_cauchy_body_concrete, magnitude_of, mul_ordered_half_body, one_c,
    promote_ordered_half_to_full, sign_abs_le_one, two, two_normalize,
};
use super::{CRealPrelude, DERIVED_HEIGHT, creal_ty, equiv};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::{ExprId, ExprNode};
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Height for `cosFnTerm`: one past `powerSeriesTerm`'s own
/// `DERIVED_HEIGHT + 43` (`creal/power.rs`), matching this development's
/// convention of giving a thin wrapper a height just past what it unfolds
/// to.
const COS_FN_TERM_HEIGHT: u16 = DERIVED_HEIGHT + 44;

/// Peel one `App` node off `e`, returning `(function, argument)`.
///
/// Used only to decompose the INFERRED type of a `weierstrassMTest`
/// application, whose shape (`UniformConvergesOn F G a b`, a 4-ary
/// application) this file controls completely by construction — this is not
/// parsing untrusted input, it is reading back a term this same function
/// just built. Panics if `e` is not an application, which would mean
/// `weierstrassMTest`'s own conclusion shape changed underneath this file.
fn unapp(d: &mut IntDev<'_>, e: ExprId) -> (ExprId, ExprId) {
    match d.kernel().expr_node(e).clone() {
        ExprNode::App(f, a) => (f, a),
        other => panic!("expected an application (UniformConvergesOn F G a b), found {other:?}"),
    }
}

/// `CReal.cosFnTerm : Nat → CReal → CReal := fun k x => mul (cosTerm k) (pow
/// x (Nat.add k k))`. See the module documentation for the route.
fn declare_cos_fn_term(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_term_k = d.apply(cos_term_c, &[k]);
    let two_k = d.add(k, k);
    let pow_x_2k = cpow(d, p, x, two_k);
    let body = cmul(d, p, cos_term_k, pow_x_2k);

    let value = {
        let with_x = d.lam_fv(x_fv, carrier, body);
        d.lam_fv(k_fv, nat, with_x)
    };
    let ty = {
        let with_x = d.arrow(carrier, carrier);
        d.arrow(nat, with_x)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cos_fn_term,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(COS_FN_TERM_HEIGHT),
    })
}

/// `CReal.cosFnTerm_congr : ∀ k x y, Equiv x y → Equiv (cosFnTerm k x)
/// (cosFnTerm k y)` — `CReal.mulPowCongr` applied at the constant coefficient
/// function `fun _ => cosTerm k` and exponent `Nat.add k k`. No new
/// congruence argument: `mulPowCongr`'s own statement is `∀ c j x y, Equiv x
/// y → Equiv (mul (c j) (pow x j)) (mul (c j) (pow y j))`, universally
/// quantified over `j`, so instantiating `j := Nat.add k k` and `c := fun _
/// => cosTerm k` (so `c j` beta-reduces to `cosTerm k`) gives exactly this
/// statement up to β/δ.
fn declare_cos_fn_term_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let heq_ty = equiv(d, p, x, y);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_term_k = d.apply(cos_term_c, &[k]);
    let dummy_fv = d.fresh_fvar();
    let const_fn = d.lam_fv(dummy_fv, nat, cos_term_k);
    let two_k = d.add(k, k);

    let proof = d.lemma(p.mul_pow_congr, &[const_fn, two_k, x, y, heq]);

    let value = {
        let with_heq = d.lam_fv(heq_fv, heq_ty, proof);
        let with_y = d.lam_fv(y_fv, carrier, with_heq);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(k_fv, nat, with_x)
    };
    let ty = {
        let cft_k_x = d.const_app(p.cos_fn_term, &[k, x]);
        let cft_k_y = d.const_app(p.cos_fn_term, &[k, y]);
        let concl = equiv(d, p, cft_k_x, cft_k_y);
        let with_heq = d.arrow(heq_ty, concl);
        let with_y = d.pi_fv(y_fv, carrier, with_heq);
        let with_x = d.pi_fv(x_fv, carrier, with_y);
        d.pi_fv(k_fv, nat, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_term_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (neg zero) zero`, reproduced from `creal/power.rs::neg_zero_equiv`
/// (private there) — see this development's established convention
/// (`creal/trig.rs::neg_zero_equiv_local`) of reproducing a sibling module's
/// private helper rather than widening its visibility.
fn neg_zero_equiv_here(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let h1 = d.lemma(p.add_zero, &[nz]); // Equiv padded nz
    let step1 = d.lemma(p.equiv_symm, &[padded, nz, h1]); // Equiv nz padded
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]); // Equiv padded (add zero nz)
    let flipped = cadd(d, p, zero_c, nz);
    let h3 = d.lemma(p.add_neg, &[zero_c]); // Equiv flipped zero
    let step2 = d.lemma(p.equiv_trans, &[nz, padded, flipped, step1, h2]);
    d.lemma(p.equiv_trans, &[nz, flipped, zero_c, step2, h3])
}

/// `le zero one`, from `zero_lt_one` + `le_of_lt` — the same two-step route
/// `creal/power.rs::declare_pow_nonneg`'s base case already uses.
fn zero_le_one(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let one_cc = one_c(d, p);
    let lt_witness = d.lemma(p.zero_lt_one, &[]);
    d.lemma(p.le_of_lt, &[zero_c, one_cc, lt_witness])
}

/// `CReal.cosFnTermAbsLe : ∀ x, le zero x → le x one → ∀ k, le (abs
/// (cosFnTerm k x)) (expDominant k)`. See the module documentation: no new
/// domination series, `pow_le_one` + `abs_mul_le_of_bounds` +
/// `cosTermAbsLeDominant` via `le_trans`.
fn declare_cos_fn_term_abs_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let one_cc = one_c(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hax_ty = cle(d, p, zero_c, x);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hxb_ty = cle(d, p, x, one_cc);
    let hxb_fv = d.fresh_fvar();
    let hxb = d.kernel().fvar(hxb_fv);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let two_k = d.add(k, k);
    let pow_x_2k = cpow(d, p, x, two_k);

    // pow_x_2k <= one, zero <= pow_x_2k
    let h_le_one = d.lemma(p.pow_le_one, &[x, hax, hxb, two_k]);
    let h_nonneg = d.lemma(p.pow_nonneg, &[x, hax, two_k]);

    // neg pow_x_2k <= one, via neg pow_x_2k <= neg zero ~ zero <= one.
    let neg_pow = cneg(d, p, pow_x_2k);
    let neg_zero = cneg(d, p, zero_c);
    let step1 = d.lemma(p.neg_le_neg, &[zero_c, pow_x_2k, h_nonneg]); // le neg_pow neg_zero
    let nz_eq = neg_zero_equiv_here(d, p); // Equiv neg_zero zero_c
    let refl_neg_pow = d.lemma(p.equiv_refl, &[neg_pow]);
    let neg_pow_le_zero = d.lemma(
        p.le_congr,
        &[
            neg_pow,
            neg_pow,
            neg_zero,
            zero_c,
            refl_neg_pow,
            nz_eq,
            step1,
        ],
    );
    let zlo = zero_le_one(d, p);
    let neg_pow_le_one = d.lemma(p.le_trans, &[neg_pow, zero_c, one_cc, neg_pow_le_zero, zlo]);

    let abs_pow_le_one = d.lemma(p.abs_le, &[pow_x_2k, one_cc, h_le_one, neg_pow_le_one]);

    // abs (mul (cosTerm k) pow_x_2k) <= mul (abs (cosTerm k)) one.
    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_term_k = d.apply(cos_term_c, &[k]);
    let abs_cos_term_k = cabs(d, p, cos_term_k);
    let le_refl_abs = d.lemma(p.le_refl, &[abs_cos_term_k]);
    let mul_bound = d.lemma(
        p.abs_mul_le_of_bounds,
        &[
            cos_term_k,
            pow_x_2k,
            abs_cos_term_k,
            one_cc,
            le_refl_abs,
            abs_pow_le_one,
        ],
    );

    // fold mul (abs (cosTerm k)) one ~ abs (cosTerm k) via mul_one, then
    // chain to expDominant k via cosTermAbsLeDominant.
    let mul_one_eq = d.lemma(p.mul_one, &[abs_cos_term_k]); // Equiv (mul abs_cos_term_k one) abs_cos_term_k
    let mul_term = cmul(d, p, cos_term_k, pow_x_2k);
    let lhs_abs = cabs(d, p, mul_term);
    let refl_lhs = d.lemma(p.equiv_refl, &[lhs_abs]);
    let abs_mul_one = cmul(d, p, abs_cos_term_k, one_cc);
    let mul_bound2 = d.lemma(
        p.le_congr,
        &[
            lhs_abs,
            lhs_abs,
            abs_mul_one,
            abs_cos_term_k,
            refl_lhs,
            mul_one_eq,
            mul_bound,
        ],
    );

    let dominant_k = {
        let ed = d.kernel().const_(p.exp_dominant, vec![]);
        d.apply(ed, &[k])
    };
    let cos_dom = d.lemma(p.cos_term_abs_le_dominant, &[k]);
    let final_proof = d.lemma(
        p.le_trans,
        &[lhs_abs, abs_cos_term_k, dominant_k, mul_bound2, cos_dom],
    );

    let value = {
        let with_k = d.lam_fv(k_fv, nat, final_proof);
        let with_hxb = d.lam_fv(hxb_fv, hxb_ty, with_k);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxb);
        d.lam_fv(x_fv, carrier, with_hax)
    };
    let ty = {
        let cft_k_x = d.const_app(p.cos_fn_term, &[k, x]);
        let abs_cft = cabs(d, p, cft_k_x);
        let concl = cle(d, p, abs_cft, dominant_k);
        let with_k = d.pi_fv(k_fv, nat, concl);
        let with_hxb = d.arrow(hxb_ty, with_k);
        let with_hax = d.arrow(hax_ty, with_hxb);
        d.pi_fv(x_fv, carrier, with_hax)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_term_abs_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.cosFn` and `CReal.cosFnUniformConverges`. Run after
/// `declare_cos_fn_term`/`declare_cos_fn_term_congr`/`declare_cos_fn_term_abs_le`
/// (this file), `trig::declare_trig` (`cosTerm`, `cosTermAbsLeDominant`),
/// `exponential::declare_e_family` (`expDominant`), and
/// `uniform_convergence::declare_weierstrass_m_test`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_fn(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let one_cc = one_c(d, p);

    let f0 = d.kernel().const_(p.cos_fn_term, vec![]);
    let mseq0 = d.kernel().const_(p.exp_dominant, vec![]);

    let hab0 = zero_le_one(d, p);

    // hcong0 : forall j p q, Equiv p q -> Equiv (f0 j p) (f0 j q), built
    // pointwise from `cosFnTerm_congr`.
    let hcong0 = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);
        let heq_ty = equiv(d, p, pp, qq);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let body = d.lemma(p.cos_fn_term_congr, &[j, pp, qq, heq]);
        let with_heq = d.lam_fv(heq_fv, heq_ty, body);
        let with_qq = d.lam_fv(qq_fv, carrier, with_heq);
        let with_pp = d.lam_fv(pp_fv, carrier, with_qq);
        d.lam_fv(j_fv, nat, with_pp)
    };

    // (k_g, hcauchy0) : the SAME concrete witness `cosOne` itself uses for
    // `Cauchy (sumRange expDominant)` -- already exactly `weierstrassMTest`'s
    // own `hcauchy` shape, no bridge needed.
    let (k_g, hcauchy0) = exp_dominant_cauchy_body_concrete(d, p);

    // hdom0 : forall j pt, le zero pt -> le pt one -> le (abs (f0 j pt)) (mseq0 j).
    let hdom0 = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);
        let body = d.lemma(p.cos_fn_term_abs_le, &[pt, hax, hxb, j]);
        let hax_ty = cle(d, p, zero_c, pt);
        let hxb_ty = cle(d, p, pt, one_cc);
        let with_hxb = d.lam_fv(hxb_fv, hxb_ty, body);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxb);
        let with_pt = d.lam_fv(pt_fv, carrier, with_hax);
        d.lam_fv(j_fv, nat, with_pt)
    };

    let u0 = d.lemma(
        p.weierstrass_m_test,
        &[
            f0, mseq0, zero_c, one_cc, hab0, hcong0, k_g, hdom0, hcauchy0,
        ],
    );
    let ty0 = d.kernel().infer(u0)?;

    // ty0 : UniformConvergesOn F0 G0 zero one -- peel `b`, `a`, then `G0`.
    let (inner1, _b0) = unapp(d, ty0);
    let (inner2, _a0) = unapp(d, inner1);
    let (_inner3, g0) = unapp(d, inner2);

    let cos_fn_ty = d.arrow(carrier, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cos_fn,
        uparams: vec![],
        ty: cos_fn_ty,
        value: g0,
        hint: ReducibilityHint::Regular(COS_FN_TERM_HEIGHT + 1),
    })?;

    // Big_f, restated so the ascribed `ty` reads with the same `F` this
    // theorem's own statement will show a caller.
    let big_f = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        let f_pt = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = d.const_app(p.cos_fn_term, &[j, pt]);
            d.lam_fv(j_fv, nat, body)
        };
        let body = d.const_app(p.sum_range, &[f_pt, n]);
        let with_pt = d.lam_fv(pt_fv, carrier, body);
        d.lam_fv(n_fv, nat, with_pt)
    };
    let cos_fn_c = d.kernel().const_(p.cos_fn, vec![]);
    let ty = d.const_app(p.uniform_converges_on, &[big_f, cos_fn_c, zero_c, one_cc]);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_uniform_converges,
        uparams: vec![],
        ty,
        value: u0,
    })
}

pub(super) fn declare_cos_fn_family(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_cos_fn_term(d, p)?;
    declare_cos_fn_term_congr(d, p)?;
    declare_cos_fn_term_abs_le(d, p)?;
    declare_cos_fn(d, p)
}

// ============================================================================
// Progress toward a wider cosine domain (Spivak ch. 15's π): the pointwise
// domination bound past x = 1, and the raw (non-existential) Cauchy witness
// for the ratio-16/25 dominating series. Neither is yet wired into
// `weierstrassMTest` -- see this file's own module documentation (the
// "2026-08-27 update" section) for exactly what remains and why.
// ============================================================================

/// `le (abs (cosTerm k)) (mul two (pow half (Nat.add k k)))` -- the TIGHT,
/// pre-collapse bound `CReal.cosTermAbsLeDominant`'s own proof computes
/// internally, one step before its final `exp_dominant_double_le` collapse
/// down to `expDominant k` (see `creal/trig.rs::declare_cos_term_abs_le_dominant`,
/// reproduced here up to but not including that last step). The collapsed
/// `expDominant k` bound `cos_term_abs_le_dominant` exports is too loose to
/// combine with a domain past `[0, 1]` -- see the module documentation.
///
/// Returns `(mul two (pow half (Nat.add k k)), proof)`.
fn cos_term_abs_le_dom_double(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> (ExprId, ExprId) {
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let sign_k = cpow(d, p, neg_one, k);
    let sign_abs = sign_abs_le_one(d, p, k);

    let double_k = d.add(k, k);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let e_term = d.apply(exp_term_c, &[double_k]);
    let exp_dominant_c = d.kernel().const_(p.exp_dominant, vec![]);
    let dom_double = d.apply(exp_dominant_c, &[double_k]);

    let e_dom_bound = d.lemma(p.exp_term_abs_le_dominant, &[double_k]);
    // e_dom_bound : le (abs e_term) dom_double

    let prod_bound = d.lemma(
        p.abs_mul_le_of_bounds,
        &[sign_k, e_term, one_cc, dom_double, sign_abs, e_dom_bound],
    );
    // prod_bound : le (abs (mul sign_k e_term)) (mul one_cc dom_double)

    let mul_comm_1e = d.lemma(p.mul_comm, &[one_cc, dom_double]);
    let mul_one_e = d.lemma(p.mul_one, &[dom_double]);
    let mul_one_cc_dom = cmul(d, p, one_cc, dom_double);
    let mul_dom_one = cmul(d, p, dom_double, one_cc);
    let one_dom_equiv = echain(
        d,
        p,
        mul_one_cc_dom,
        &[(mul_dom_one, mul_comm_1e), (dom_double, mul_one_e)],
    );

    let cos_term_k = cmul(d, p, sign_k, e_term);
    let abs_cos_term_k = cabs(d, p, cos_term_k);
    let refl_abs_cos = erefl(d, p, abs_cos_term_k);
    let abs_cos_le_dom_double = d.lemma(
        p.le_congr,
        &[
            abs_cos_term_k,
            abs_cos_term_k,
            mul_one_cc_dom,
            dom_double,
            refl_abs_cos,
            one_dom_equiv,
            prod_bound,
        ],
    );

    (dom_double, abs_cos_le_dom_double)
}

/// `CReal.cosFnTermAbsLeWide : ∀ x, le zero x → ∀ R, le x R → ∀ k, le (abs
/// (cosFnTerm k x)) (mul (expDominant (Nat.add k k)) (pow R (Nat.add k
/// k)))`. See the module documentation's "2026-08-27 update" section: `0 ≤
/// x ≤ R` for ANY `R` (`le zero R` derived by `le_trans` from the two
/// hypotheses, not a separate parameter) via
/// [`CRealPrelude::exp_term_abs_le_dominant`] at the doubled index (through
/// [`cos_term_abs_le_dom_double`]) plus
/// [`CRealPrelude::pow_le_pow_of_base_le`] (base monotonicity), combined by
/// [`CRealPrelude::abs_mul_le_of_bounds`] -- no new domination series,
/// exactly as the task brief predicted. This does NOT reduce the bound to
/// the literal ratio `16/25` -- doing that needs `pow a n * pow b n ≈ pow
/// (mul a b) n`, an identity this kernel does not have; see the module
/// documentation for exactly what remains.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_fn_term_abs_le_wide(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hax_ty = cle(d, p, zero_c, x);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);

    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let hxr_ty = cle(d, p, x, r);
    let hxr_fv = d.fresh_fvar();
    let hxr = d.kernel().fvar(hxr_fv);

    let hr0 = d.lemma(p.le_trans, &[zero_c, x, r, hax, hxr]);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let two_k = d.add(k, k);
    let pow_x_2k = cpow(d, p, x, two_k);
    let pow_r_2k = cpow(d, p, r, two_k);

    let (dom_double_k, abs_cos_le_dom_double) = cos_term_abs_le_dom_double(d, p, k);

    // pow_x_2k <= pow_r_2k, zero <= pow_r_2k, zero <= pow_x_2k.
    let pow_bound = d.lemma(p.pow_le_pow_of_base_le, &[x, r, hax, hxr, two_k]);
    let pow_r_nonneg = d.lemma(p.pow_nonneg, &[r, hr0, two_k]);
    let pow_x_nonneg = d.lemma(p.pow_nonneg, &[x, hax, two_k]);

    // neg pow_x_2k <= pow_r_2k, via neg pow_x_2k <= neg zero ~ zero <= pow_r_2k.
    let neg_pow = cneg(d, p, pow_x_2k);
    let neg_zero = cneg(d, p, zero_c);
    let step1 = d.lemma(p.neg_le_neg, &[zero_c, pow_x_2k, pow_x_nonneg]); // le neg_pow neg_zero
    let nz_eq = neg_zero_equiv_here(d, p); // Equiv neg_zero zero_c
    let refl_neg_pow = d.lemma(p.equiv_refl, &[neg_pow]);
    let neg_pow_le_zero = d.lemma(
        p.le_congr,
        &[
            neg_pow,
            neg_pow,
            neg_zero,
            zero_c,
            refl_neg_pow,
            nz_eq,
            step1,
        ],
    );
    let neg_pow_le_r = d.lemma(
        p.le_trans,
        &[neg_pow, zero_c, pow_r_2k, neg_pow_le_zero, pow_r_nonneg],
    );

    let abs_pow_le_r = d.lemma(p.abs_le, &[pow_x_2k, pow_r_2k, pow_bound, neg_pow_le_r]);

    // abs (mul (cosTerm k) pow_x_2k) <= mul dom_double_k pow_r_2k.
    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_term_k = d.apply(cos_term_c, &[k]);
    let mul_bound = d.lemma(
        p.abs_mul_le_of_bounds,
        &[
            cos_term_k,
            pow_x_2k,
            dom_double_k,
            pow_r_2k,
            abs_cos_le_dom_double,
            abs_pow_le_r,
        ],
    );

    let value = {
        let with_k = d.lam_fv(k_fv, nat, mul_bound);
        let with_hxr = d.lam_fv(hxr_fv, hxr_ty, with_k);
        let with_r = d.lam_fv(r_fv, carrier, with_hxr);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_r);
        d.lam_fv(x_fv, carrier, with_hax)
    };
    let ty = {
        let cft_k_x = d.const_app(p.cos_fn_term, &[k, x]);
        let abs_cft = cabs(d, p, cft_k_x);
        let bound = cmul(d, p, dom_double_k, pow_r_2k);
        let concl = cle(d, p, abs_cft, bound);
        let with_k = d.pi_fv(k_fv, nat, concl);
        let with_hxr = d.arrow(hxr_ty, with_k);
        let with_r = d.pi_fv(r_fv, carrier, with_hxr);
        let with_hax = d.arrow(hax_ty, with_r);
        d.pi_fv(x_fv, carrier, with_hax)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_term_abs_le_wide,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.cosDominant16Over25 : Nat → CReal := fun k => mul two (pow
/// (ofRat (natDivSucc 16 24)) k)` -- the dominating series for a wider
/// cosine domain (ratio `16/25 = (4/5)²`, `R := 8/5` clears cosine's first
/// zero; see `creal/geometric.rs::ratio_16_over_25_witnesses`'s own doc
/// comment for the derivation).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_dominant_16_over_25(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let (x, ..) = ratio_16_over_25_witnesses(d, p);
    let two_creal = two(d, p);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let pow_x_k = cpow(d, p, x, k);
    let body = cmul(d, p, two_creal, pow_x_k);

    let value = d.lam_fv(k_fv, nat, body);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cos_dominant_16_over_25,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(COS_FN_TERM_HEIGHT + 2),
    })
}

/// `λ n, CReal.pow x n`, reproduced verbatim from `geometric.rs`'s own
/// private `pow_fn` (Rust privacy: sibling module; `geometric.rs` is
/// off-limits to edit this slice, so its `fn` cannot be widened).
fn pow_fn_local(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let body = cpow(d, p, x, n);
    d.lam_fv(n_fv, nat, body)
}

/// `((25*25)+1)+7`, reproduced verbatim from `geometric.rs`'s own private
/// `geom_cauchy_of_lt_k_final` at `bigk := (Nat.succ n24)*(Nat.succ n24)`
/// -- the concrete modulus `CReal.geomCauchyOrdered16Over25`'s own
/// conclusion uses internally. Recomputed here from the SAME `Nat` builder
/// calls (rather than imported: `geometric.rs` is off-limits to edit this
/// slice, so its private `fn` cannot be widened), so the result is defeq to
/// -- and, since the arena structurally hashes, almost certainly the
/// identical `ExprId` as -- what `mul_ordered_half_body`'s own bookkeeping
/// needs to match against.
fn geom_16_over_25_k_final(d: &mut IntDev<'_>, n24: ExprId) -> ExprId {
    let succ24 = d.succ(n24);
    let bigk = NatOps::mul(d, succ24, succ24);
    let one_nat = d.num(1);
    let big_k1 = d.add(bigk, one_nat);
    let seven_nat = d.num(7);
    d.add(big_k1, seven_nat)
}

/// A CONCRETE `(K, proof : sum_range_cauchy_body (sumRange
/// cosDominant16Over25) K)` -- the "constant-2 scaling" step named in the
/// task brief, at ratio `16/25` instead of `1/2`. Built via
/// [`mul_ordered_half_body`] (`c := two`, `q := two`'s own rational, `s :=
/// pow_fn_local x`, `k_s := geom_16_over_25_k_final`) against
/// `CReal.geomCauchyOrdered16Over25` (already raw, non-existential) as the
/// base series' own ordered-half witness, plus
/// [`promote_ordered_half_to_full`]'s `Nat.le_total` promotion -- verbatim
/// in technique to `exponential.rs`/`trig.rs`'s own
/// `exp_dominant_cauchy_body_concrete`, confirmed to finish UNCHANGED once
/// widened to `pub(super)`, exactly as the task brief predicted.
fn cos_dominant_16_over_25_cauchy_body_concrete(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let (x, _, _, _, n24, _, _) = ratio_16_over_25_witnesses(d, p);
    let raw_pow_x = pow_fn_local(d, p, x);
    let s_fn = d.const_app(p.sum_range, &[raw_pow_x]);
    let two_creal = two(d, p);
    let (two_rat, _, _) = two_normalize(d, p);

    let k_s = geom_16_over_25_k_final(d, n24);
    let two_nat = d.num(2);
    let ka = magnitude_of(d, p, two_creal);
    let kg_num = NatOps::mul(d, ka, k_s);
    let ka2 = NatOps::mul(d, ka, two_nat);
    let k_g = d.add(kg_num, ka2);

    // `G := fun n => mul two (S n)`, `S := sumRange (pow (16/25) ·)`.
    let g_fn = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.apply(s_fn, &[n]);
        let prod = cmul(d, p, two_creal, sn);
        d.lam_fv(n_fv, nat, prod)
    };

    let ordered_half = |d: &mut IntDev<'_>, a: ExprId, b: ExprId, hab: ExprId| -> ExprId {
        let (_, proof) = mul_ordered_half_body(
            d,
            p,
            two_creal,
            two_rat,
            s_fn,
            k_s,
            a,
            b,
            &|d, aa, bb, hh| d.lemma(p.geom_cauchy_ordered_16_over_25, &[aa, bb, hh]),
            hab,
        );
        proof
    };

    // Concrete `Cauchy G` at `k_g` -- `G` itself, not yet `sumRange
    // cosDominant16Over25` (only `Equiv`, via `CReal.mul_sumRange`).
    let g_case_proof = promote_ordered_half_to_full(d, p, g_fn, k_g, &ordered_half);

    // Transport across `mul_sumRange`'s `Equiv` onto `F := sumRange
    // cosDominant16Over25` -- the same transport [`declare_cauchy_of_pointwise_equiv`]
    // performs, but concrete (`cauchy_body_transport`, not wrapped in
    // `Exists`), because `K` is needed as DATA here.
    let cos_dominant_const = d.kernel().const_(p.cos_dominant_16_over_25, vec![]);
    let f_fn = d.const_app(p.sum_range, &[cos_dominant_const]);
    let heq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.lemma(p.mul_sum_range, &[two_creal, raw_pow_x, n]);
        d.lam_fv(n_fv, nat, body)
    };

    cauchy_body_transport(d, p, g_fn, f_fn, heq, k_g, g_case_proof)
}

/// `CReal.cosDominant16Over25CauchyBody : sum_range_cauchy_body (sumRange
/// cosDominant16Over25) K` for the concrete `K`
/// [`cos_dominant_16_over_25_cauchy_body_concrete`] returns -- the raw,
/// non-existential Cauchy witness `weierstrassMTest`'s `hcauchy` parameter
/// needs, at ratio `16/25`. See the module documentation's "2026-08-27
/// update" section for what still separates this from an application of
/// `weierstrassMTest` to a wider `cosFn`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_dominant_16_over_25_cauchy_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let (k_final, proof) = cos_dominant_16_over_25_cauchy_body_concrete(d, p);
    let cos_dominant_const = d.kernel().const_(p.cos_dominant_16_over_25, vec![]);
    let f_fn = d.const_app(p.sum_range, &[cos_dominant_const]);
    let ty = sum_range_cauchy_body(d, p, f_fn, k_final);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_dominant_16_over_25_cauchy_body,
        uparams: vec![],
        ty,
        value: proof,
    })
}

/// Admit the wider-cosine PROGRESS pieces: the pointwise domination bound
/// past `[0, 1]` and the ratio-`16/25` dominating series' raw Cauchy
/// witness. Does NOT apply `weierstrassMTest` -- see the module
/// documentation's "2026-08-27 update" section for exactly why, and what
/// remains.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_fn_wide_progress(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_cos_fn_term_abs_le_wide(d, p)?;
    declare_cos_dominant_16_over_25(d, p)?;
    declare_cos_dominant_16_over_25_cauchy_body(d, p)
}
