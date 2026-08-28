//! **`CReal.cosFn : CReal → CReal`** — general cosine as a genuine function,
//! on the bounded domain `[0, 1]`, via the power series `Σ (-1)^k x^{2k} /
//! (2k)!`. This is the piece `creal/trig.rs`'s own module documentation
//! named as out of scope for `CReal.cosOne` (a single constant, `cos 1`):
//! the general function needed a bound depending on `|x|`, i.e. a power
//! series argument, which `creal/uniform_convergence.rs`'s
//! `weierstrassMTest`/`powerSeriesUniformConvergesOn` now supply.
//!
//! ## 2026-08-27, second update: `CReal.cosFnWide` is landed, on `[0, 8/5]`
//!
//! The "2026-08-27 update" section below (kept verbatim as the diagnosis
//! that got here) ends by naming exactly two missing pieces: a general `pow
//! a n · pow b n ≈ pow (a·b) n` identity, and a concrete `Rat` computation
//! `(1/2 · 8/5)² = 16/25`. **Both are now built and both are confirmed by
//! the kernel** (`creal_prelude_builds` green, `every_creal_declaration_is_
//! checked_and_axiom_free` green):
//!
//! - [`declare_pow_mul_distrib`] (`CReal.powMulDistrib`) — the general
//!   identity, by induction on `n` mirroring `power.rs::declare_pow_add`'s
//!   own shape ([`mul_pqab_shuffle`] is the four-factor
//!   commute-and-reassociate step the induction's `succ` case needs).
//!   Declared here rather than in `power.rs` (out of this task's scope to
//!   edit) but general in `a`, `b`, `n` — not tied to this file's ratio.
//! - [`half_r_squared_eq_16_over_25`] — the concrete `Rat` bridge, via
//!   `Rat.normalize_mul_normalize` (fusing `1/2 · 8/5` into a single
//!   `normalize`, then squaring it) and `Rat.normalize_congr` (reducing
//!   `8/10` to `4/5` BEFORE squaring, so the square lands directly on
//!   `normalize 16 25` — `natDivSucc 16 24`'s own literal form — with no
//!   further reduction needed). Every intermediate representative is read
//!   back off the actual lemma applications via [`req_sides`]/[`two_sides`],
//!   never hand-reconstructed — the same technique [`declare_cos_fn`] itself
//!   already uses to extract `weierstrassMTest`'s `G`.
//!
//! [`wide_bound_bridge`] combines both to relate
//! [`declare_cos_fn_term_abs_le_wide`]'s raw pointwise bound to
//! [`declare_cos_dominant_16_over_25`]'s exact dominating-series shape, and
//! [`declare_cos_fn_wide`] applies `weierstrassMTest` at that bridge to
//! admit `CReal.cosFnWide : CReal → CReal` and `CReal.cosFnWideUniformConverges`
//! on `[0, R]`, `R := ofRat (natDivSucc 8 4) = 8/5` — chosen because it
//! clears cosine's first zero (`≈ 1.5708`), which was the entire point of
//! extending the domain past `[0, 1]` (Spivak ch. 15's `π`). **This is a
//! SEPARATE declaration from [`CReal.cosFn`] (`[0, 1]`), not a widening of
//! it** — every existing `[0, 1]` caller of `cosFn` is untouched; a reader
//! auditing this choice should confirm `cos_fn`'s own field/`BuildStep`
//! entries are unchanged by this diff, which they are.
//!
//! **What this does NOT reach — read the "What is NOT built here" and
//! "Investigated for π" sections below as still current in substance, only
//! their opening premise ("nothing here changes the domain") is now
//! false-by-supersession.** `cosFnWide 1 ≡ cosOne`/`cosFn` compatibility,
//! `sinFn`, `cosFnWide`'s own `UniformlyContinuousOn`, and any refutation or
//! construction of an EXACT root are exactly as absent as before — none of
//! today's work touches `creal/ivt.rs`, and `ivt_approx`'s family is still
//! the only root-finding route this kernel has, still approximate-only, per
//! ADR-0603 Amendment 4. **An approximate π must never be named as if
//! exact**, and today's work does not change that boundary at all — it only
//! moves the DOMAIN a genuine function is defined on.
//!
//! ## 2026-08-27, third update: `CReal.cosFnWideUniformlyContinuous` is
//! landed
//!
//! [`declare_cos_fn_wide_uniformly_continuous`] admits
//! `UniformlyContinuousOn cosFnWide zero R` via
//! `CReal.uniform_limit_uniformly_continuous` applied at
//! `CReal.cosFnWideUniformConverges`. Its own second hypothesis, `∀ n,
//! UniformlyContinuousOn (F n) zero R`, was NOT free-standing anywhere in
//! the tree and is built here by a genuine `Nat.rec` induction on `n` at
//! `level_one` ([`induct_ty`] -- `UniformlyContinuousOn` is `Type`-valued,
//! so the trait's own `NatOps::induct` at `level_zero` does not apply). The
//! step case needs `UniformlyContinuousOn (cosFnTerm n ·) zero R` for the
//! CURRENT induction variable ([`cos_fn_term_uc`]), which itself needs `pow`
//! uniform continuity at a symbolic exponent -- a SEPARATE, nested
//! induction over the base, built once up front
//! ([`declare_cos_fn_wide_uniformly_continuous`]'s own `pow_uc`) and applied
//! at `Nat.add n n`. Every `BoundedOn` hypothesis either induction needs
//! comes from the already-public `CReal.bounded_of_uniformly_continuous`
//! ([`bounded_via_uc`]), never hand-derived.
//!
//! **`Kernel::infer` alone cannot type an application built inside an open
//! induction step** -- it uses a FRESH, empty context, so a term mentioning
//! the step's own still-open `j`/`ih` free variables is rejected
//! `UnboundFVar`, not merely imprecise. [`bounded_via_uc`] registers those
//! as [`LocalDecl`]s in a scratch [`LocalContext`] and calls
//! `Kernel::infer_in` instead -- the same mechanism `declare_cos_fn_wide`'s
//! own `unapp`-based extraction uses on a CLOSED term, extended to an open
//! one.
//!
//! **What this does NOT reach.** `ivt_approx` (`creal/ivt.rs`, out of this
//! file's scope) still needs a sign-change witness at `cosFnWide`'s two
//! endpoints before an approximate root family exists at all, and even
//! then `ivt_approx`'s own conclusion is `∀ e, ∃ x, …` -- an
//! APPROXIMATE-root family, never `cosFnWide c ≡ zero`. Nothing here
//! constructs or refutes an exact root; ADR-0603 Amendment 4 is unchanged.
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
//! ## `cosFn 1 ≡ cosOne` — landed (2026-08-27)
//!
//! `CReal.cosFn_one_equiv_cosOne : Equiv (cosFn one) cosOne`,
//! [`declare_cos_fn_equiv_cos_one`] below — the mechanical sibling of
//! `creal/exp_fn.rs::declare_exp_fn_one_equiv_e`, predicted (and confirmed)
//! to transport step for step. The blocker this section used to name here —
//! "no public bridge from `close_within` back to the sample-level `Within`
//! `Converges` needs" — was never real: `CReal.close_within_of_within`
//! (`creal/uniform_convergence.rs`, via `close_within_of_within_at`) already
//! runs the FORWARD direction (`Within` to `close_within`) this bridge
//! needs, confirmed first for `expFn 1 ≡ e` and unchanged here. The one real
//! difference from the `expFn` template: `cosFnTerm` is this file's own
//! even-only wrapper (`cosFnTerm k x := mul (cosTerm k) (pow x (Nat.add k
//! k))`), not a `CReal.powerSeriesTerm` partial application, so leg 2's
//! transport (`cosFnTerm j one ≡ cosTerm j`) is built directly against
//! `cosFnTerm` ([`cos_fn_term_one_equiv`]) rather than through
//! `powerSeriesTerm_one_equiv`'s generic route — otherwise identical
//! (`pow_one_equiv` itself is exponent-generic and reused verbatim).
//! Verified against the kernel (`creal_prelude_builds` and
//! `every_creal_declaration_is_checked_and_axiom_free`), not merely `cargo
//! check`.
//!
//! ## What is NOT built here
//!
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
//!
//! **SUPERSEDED — see the "2026-08-27, second update" section above this
//! one.** Both named gaps are now built and `CReal.cosFnWide` is landed on
//! `[0, 8/5]`. This paragraph is kept because the diagnosis leading to it
//! (why the bridge was hard, why it is NOT the same as the "unchanged, just
//! widened" prediction) is still the correct explanation of the shape of
//! the work — only its concluding sentence is now false.

use super::convergence::{converges_predicate, div_succ_at};
use super::derivative::{
    abs_le_of_equiv, hd_ty, le_abs_neg_of_le_abs, mul_neg_equiv, neg_add_distrib,
    neg_mul_equiv_left, pow_deriv_fn, pow_succ_fn,
};
use super::geometric::ratio_16_over_25_witnesses;
use super::series::sum_range_cauchy_body;
use super::trig::{
    cabs, cadd, cauchy_body_transport, cle, cmul, cneg, cpow, czero, double_neg, echain, erefl,
    esymm, exp_dominant_cauchy_body_concrete, magnitude_of, mul_ordered_half_body, neg_add_self,
    one_c, promote_ordered_half_to_full, sign_abs_le_one, two, two_normalize,
};
use super::uniform_convergence::close_within_of_within_at;
use super::{CRealPrelude, DERIVED_HEIGHT, creal_ty, embed, equiv};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::{ExprId, ExprNode};
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{normalize, one_le_succ, radd, rat_eq_rewrite, rchain, rtrans};
use crate::tc::{LocalContext, LocalDecl};

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
pub(super) fn unapp(d: &mut IntDev<'_>, e: ExprId) -> (ExprId, ExprId) {
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
/// `fun n pt => sumRange (fun j => cosFnTerm j pt) n` -- the partial-sum
/// sequence both [`declare_cos_fn`] (domain `[0, 1]`) and
/// [`declare_cos_fn_wide`] (domain `[0, R]`) ascribe their own
/// `cosFnUniformConverges`/`cosFnWideUniformConverges` theorems against.
/// Factored into one builder so every caller reconstructs the IDENTICAL
/// term (same builder calls, so the same `ExprId` by structural hashing) --
/// this file's established convention, see e.g.
/// [`geom_16_over_25_k_final`]'s own doc comment -- rather than three
/// independently hand-copied blocks drifting apart.
fn cos_fn_partial_sums_fn(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    nat: ExprId,
) -> ExprId {
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
}

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
    let big_f = cos_fn_partial_sums_fn(d, p, carrier, nat);
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

// ---------------------------------------------------------------------------
// `CReal.cosFn_one_equiv_cosOne : Equiv (cosFn one) cosOne` — the mechanical
// sibling of `creal/exp_fn.rs::declare_exp_fn_equiv_e`, following that
// file's route step for step (see this file's own module documentation,
// "What is NOT built here", now stale on this point — `creal/exp_fn.rs`'s
// 2026-08-27 corrections apply here unchanged: `close_within_of_within`'s
// own per-index builder already bridges `Within` to `close_within` in the
// FORWARD direction this needs, and `equiv_zero_of_rate` already
// generalizes past rate `1`, so neither blocker this module doc once named
// is live). `echain`/`erefl`/`esymm`/`neg_add_self`/`double_neg` are reused
// directly from `creal/trig.rs` (already `pub(super)` there); the remaining
// helpers below are reproduced (Rust privacy — `creal/exp_fn.rs`'s copies
// are private) rather than imported, matching this development's
// established convention for a sibling module's private helper.
// ---------------------------------------------------------------------------

/// `Equiv a b` from `h : Equiv (add a (neg b)) zero`. Reproduced (Rust
/// privacy) from `creal/exp_fn.rs`'s own private `equiv_of_sub_equiv_zero`
/// (itself reproduced there from `creal/monotone.rs`/`creal/deriv_unique.rs`).
fn equiv_of_sub_equiv_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let nb = cneg(d, p, b);
    let diff = cadd(d, p, a, nb);
    let lhs = cadd(d, p, diff, b);
    let zero_c = czero(d, p);

    let a_from_lhs = {
        let assoc = d.lemma(p.add_assoc, &[a, nb, b]);
        let nb_b = cadd(d, p, nb, b);
        let a_nbb = cadd(d, p, a, nb_b);
        let nas = neg_add_self(d, p, b);
        let refl_a = erefl(d, p, a);
        let cong = d.lemma(p.add_congr, &[a, a, nb_b, zero_c, refl_a, nas]);
        let a_zero = cadd(d, p, a, zero_c);
        let trim = d.lemma(p.add_zero, &[a]);
        echain(d, p, lhs, &[(a_nbb, assoc), (a_zero, cong), (a, trim)])
    };
    let b_from_lhs = {
        let refl_b = erefl(d, p, b);
        let cong = d.lemma(p.add_congr, &[diff, zero_c, b, b, h, refl_b]);
        let zero_b = cadd(d, p, zero_c, b);
        let comm = d.lemma(p.add_comm, &[zero_c, b]);
        let b_zero = cadd(d, p, b, zero_c);
        let trim = d.lemma(p.add_zero, &[b]);
        echain(d, p, lhs, &[(zero_b, cong), (b_zero, comm), (b, trim)])
    };
    let a_from_lhs_symm = esymm(d, p, lhs, a, a_from_lhs);
    d.lemma(p.equiv_trans, &[a, lhs, b, a_from_lhs_symm, b_from_lhs])
}

/// From `h : le (abs w) bound`, derive `le (abs (neg w)) bound`. Reproduced
/// (Rust privacy) from `creal/exp_fn.rs`'s own private `abs_neg_le` (itself
/// reproduced there from `creal/uniform_continuity.rs`). Uses
/// `creal/trig.rs::double_neg` directly rather than a further private copy.
fn abs_neg_le(d: &mut IntDev<'_>, p: CRealPrelude, w: ExprId, q: ExprId, h: ExprId) -> ExprId {
    let abs_w = cabs(d, p, w);
    let neg_w = cneg(d, p, w);
    let w_le_absw = d.lemma(p.le_abs_self, &[w]);
    let w_le_q = d.lemma(p.le_trans, &[w, abs_w, q, w_le_absw, h]);
    let negw_le_absw = d.lemma(p.neg_le_abs, &[w]);
    let negw_le_q = d.lemma(p.le_trans, &[neg_w, abs_w, q, negw_le_absw, h]);

    let neg_neg_w = cneg(d, p, neg_w);
    let nn = double_neg(d, p, w); // Equiv neg_neg_w w
    let nn_symm = esymm(d, p, neg_neg_w, w, nn); // Equiv w neg_neg_w
    let refl_q = erefl(d, p, q);
    let nnw_le_q = d.lemma(p.le_congr, &[w, neg_neg_w, q, q, nn_symm, refl_q, w_le_q]);

    d.lemma(p.abs_le, &[neg_w, q, negw_le_q, nnw_le_q])
}

/// From `h : close_within x y q`, derive `close_within y x q`. Reproduced
/// (Rust privacy) from `creal/exp_fn.rs`'s own private `close_within_symm`.
fn close_within_symm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let ny = cneg(d, p, y);
    let nx = cneg(d, p, x);
    let diff = cadd(d, p, x, ny);
    let diff2 = cadd(d, p, y, nx);
    let abs_neg_diff_le = abs_neg_le(d, p, diff, q, h);
    let swap = d.lemma(p.neg_sub_swap, &[x, y]); // Equiv (neg diff) diff2
    let neg_diff = cneg(d, p, diff);
    let ac = d.lemma(p.abs_congr, &[neg_diff, diff2, swap]);
    let refl_q = erefl(d, p, q);
    let abs_neg_diff = cabs(d, p, neg_diff);
    let abs_diff2 = cabs(d, p, diff2);
    d.lemma(
        p.le_congr,
        &[abs_neg_diff, abs_diff2, q, q, ac, refl_q, abs_neg_diff_le],
    )
}

/// `Equiv (add zero w) w`. Reproduced (Rust privacy) from
/// `creal/exp_fn.rs`'s own private `zero_add_proof`.
fn zero_add_proof(d: &mut IntDev<'_>, p: CRealPrelude, w: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let zw = cadd(d, p, zero_c, w);
    let wz = cadd(d, p, w, zero_c);
    let comm = d.lemma(p.add_comm, &[zero_c, w]);
    let az = d.lemma(p.add_zero, &[w]);
    d.lemma(p.equiv_trans, &[zw, wz, w, comm, az])
}

/// `Equiv (add (neg u) (add u w)) w`. Reproduced (Rust privacy) from
/// `creal/exp_fn.rs`'s own private `cancel_neg_add`.
fn cancel_neg_add(d: &mut IntDev<'_>, p: CRealPrelude, u: ExprId, w: ExprId) -> ExprId {
    let nu = cneg(d, p, u);
    let nu_u = cadd(d, p, nu, u);
    let inner = cadd(d, p, u, w);
    let lhs = cadd(d, p, nu, inner);
    let nu_u_w = cadd(d, p, nu_u, w);
    let assoc = d.lemma(p.add_assoc, &[nu, u, w]); // Equiv nu_u_w lhs
    let assoc_symm = esymm(d, p, nu_u_w, lhs, assoc);
    let nas = neg_add_self(d, p, u); // Equiv nu_u zero
    let zero_c = czero(d, p);
    let refl_w = erefl(d, p, w);
    let congr1 = d.lemma(p.add_congr, &[nu_u, zero_c, w, w, nas, refl_w]);
    let zero_w = cadd(d, p, zero_c, w);
    let za = zero_add_proof(d, p, w);
    echain(
        d,
        p,
        lhs,
        &[(nu_u_w, assoc_symm), (zero_w, congr1), (w, za)],
    )
}

/// `Equiv (add (add e (neg x1)) (add x1 (neg g))) (add e (neg g))` — the
/// shared-`x1` cancellation the two `close_within` legs need to fuse into
/// one `e - g` bound. Reproduced (Rust privacy) from `creal/exp_fn.rs`'s own
/// private `diff_regroup`.
fn diff_regroup(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    e_const: ExprId,
    x1: ExprId,
    g: ExprId,
) -> ExprId {
    let ne_x1 = cneg(d, p, x1);
    let a1 = cadd(d, p, e_const, ne_x1);
    let ng = cneg(d, p, g);
    let d2 = cadd(d, p, x1, ng);
    let lhs = cadd(d, p, a1, d2);

    let inner_sum = cadd(d, p, ne_x1, d2);
    let mid = cadd(d, p, e_const, inner_sum);
    let assoc = d.lemma(p.add_assoc, &[e_const, ne_x1, d2]); // Equiv lhs mid

    let inner_cancel = cancel_neg_add(d, p, x1, ng); // Equiv inner_sum ng
    let refl_e = erefl(d, p, e_const);
    let congr_outer = d.lemma(
        p.add_congr,
        &[e_const, e_const, inner_sum, ng, refl_e, inner_cancel],
    );
    let target = cadd(d, p, e_const, ng);
    echain(d, p, lhs, &[(mid, assoc), (target, congr_outer)])
}

/// From `proof1_symm : le (abs (add e (neg x1))) q1` and `proof2 : le (abs
/// (add x1 (neg g))) q2`, derive `le (abs (add e (neg g))) (add q1 q2)` —
/// the triangle-inequality combination of the two `close_within` legs
/// sharing the midpoint `x1`. Reproduced (Rust privacy) from
/// `creal/exp_fn.rs`'s own private `combine_two_legs`.
#[allow(clippy::too_many_arguments)]
fn combine_two_legs(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    e_const: ExprId,
    x1: ExprId,
    g: ExprId,
    q1_embed: ExprId,
    q2_embed: ExprId,
    proof1_symm: ExprId,
    proof2: ExprId,
) -> ExprId {
    let ne_x1 = cneg(d, p, x1);
    let a1 = cadd(d, p, e_const, ne_x1);
    let ng = cneg(d, p, g);
    let d2 = cadd(d, p, x1, ng);
    let lhs = cadd(d, p, a1, d2);

    let abs_a1 = cabs(d, p, a1);
    let abs_d2 = cabs(d, p, d2);
    let triangle = d.lemma(p.abs_add_le, &[a1, d2]); // le (abs lhs) (add abs_a1 abs_d2)
    let combined_bound = d.lemma(
        p.add_le_add,
        &[abs_a1, q1_embed, abs_d2, q2_embed, proof1_symm, proof2],
    );
    let bound_sum = cadd(d, p, q1_embed, q2_embed);
    let abs_ab = cadd(d, p, abs_a1, abs_d2);
    let abs_lhs = cabs(d, p, lhs);
    let chain_le = d.lemma(
        p.le_trans,
        &[abs_lhs, abs_ab, bound_sum, triangle, combined_bound],
    );

    let identity = diff_regroup(d, p, e_const, x1, g); // Equiv lhs target
    let target = cadd(d, p, e_const, ng);
    let abs_identity = d.lemma(p.abs_congr, &[lhs, target, identity]);
    let refl_bound = erefl(d, p, bound_sum);
    let abs_target = cabs(d, p, target);
    d.lemma(
        p.le_congr,
        &[
            abs_lhs,
            abs_target,
            bound_sum,
            bound_sum,
            abs_identity,
            refl_bound,
            chain_le,
        ],
    )
}

/// `Equiv (pow one j) one`, for any `j` (including symbolic). Reproduced
/// (Rust privacy) from `creal/exp_fn.rs`'s own private `pow_one_equiv` —
/// not specific to `expTerm`, reused here verbatim for `cosFnTerm`'s own
/// exponent `Nat.add j j`.
fn pow_one_equiv(d: &mut IntDev<'_>, p: CRealPrelude, j: ExprId) -> ExprId {
    let one_cc = one_c(d, p);
    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let pow_v = cpow(d, p, one_cc, v);
        equiv(d, p, pow_v, one_cc)
    };
    d.induct(
        &motive,
        &|d| d.lemma(p.equiv_refl, &[one_cc]),
        &|d, j, ih| {
            let pow_j = cpow(d, p, one_cc, j);
            let mul_pow_j_one = cmul(d, p, pow_j, one_cc);
            let step1 = d.lemma(p.mul_one, &[pow_j]); // Equiv mul_pow_j_one pow_j
            d.lemma(p.equiv_trans, &[mul_pow_j_one, pow_j, one_cc, step1, ih])
        },
        j,
    )
}

/// `Equiv (cosFnTerm j one) (cosTerm j)` — `cosFnTerm j x := mul (cosTerm j)
/// (pow x (Nat.add j j))`, so at `x := one`, `pow one (Nat.add j j) ≡ one`
/// ([`pow_one_equiv`], generic in the exponent) transported through
/// `mul_congr`, then `mul_one`. Unlike `creal/exp_fn.rs`'s own
/// `power_series_term_one_equiv`, this goes through `cosFnTerm` DIRECTLY
/// rather than the generic `CReal.powerSeriesTerm`: `cosFnTerm` is this
/// file's own even-only wrapper (see the module documentation), so there is
/// no generic `powerSeriesTerm c j x` to transport through here.
fn cos_fn_term_one_equiv(d: &mut IntDev<'_>, p: CRealPrelude, j: ExprId) -> ExprId {
    let one_cc = one_c(d, p);
    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_term_j = d.apply(cos_term_c, &[j]);
    let two_j = d.add(j, j);
    let pow_one_2j = cpow(d, p, one_cc, two_j);
    let pow_eq = pow_one_equiv(d, p, two_j);
    let refl_ctj = d.lemma(p.equiv_refl, &[cos_term_j]);
    let mul_congr_step = d.lemma(
        p.mul_congr,
        &[cos_term_j, cos_term_j, pow_one_2j, one_cc, refl_ctj, pow_eq],
    );
    let mul_one_step = d.lemma(p.mul_one, &[cos_term_j]);
    let mul_pow = cmul(d, p, cos_term_j, pow_one_2j);
    let mul_one_term = cmul(d, p, cos_term_j, one_cc);
    d.lemma(
        p.equiv_trans,
        &[
            mul_pow,
            mul_one_term,
            cos_term_j,
            mul_congr_step,
            mul_one_step,
        ],
    )
}

/// `(statement, proof)` for `Equiv (G one) cosOne`, where `G` is the uniform
/// limit named by `u_conv : UniformConvergesOn F G a b` and `one` lies in
/// `[a, b]` by `hab_lo : le a one` / `hab_hi : le one b`.
///
/// Mirrors `creal/exp_fn.rs::declare_exp_fn_equiv_e` step for step: eliminate
/// `CReal.cosOneConverges`'s `Exists` witness into a per-`n` `Within` fact,
/// bridge it to `close_within` via [`close_within_of_within_at`] (leg 1),
/// transport `u_conv`'s own `.spec` at `x := one` from `cosFnTerm j one` to
/// `cosTerm j` via [`cos_fn_term_one_equiv`] + `CReal.sumRange_congr`
/// (leg 2), combine the two legs by the triangle inequality
/// ([`combine_two_legs`]), and close with `CReal.equiv_zero_of_rate` +
/// [`equiv_of_sub_equiv_zero`].
///
/// **Nothing here mentions the interval**: both legs bound the SAME partial
/// sums, so the only place `[a, b]` enters is the two range hypotheses fed to
/// `.spec`. That is why one body serves both `CReal.cosFn` (on `[0, 1]`) and
/// `CReal.cosFnWide` (on `[0, 8/5]`) — see [`declare_cos_fn_equiv_cos_one`]
/// and [`declare_cos_fn_wide_at_one`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn cos_limit_at_one_equiv_cos_one(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u_conv: ExprId,
    hab_lo: ExprId,
    hab_hi: ExprId,
) -> Result<(ExprId, ExprId), KernelError> {
    let nat = d.nat_ty();
    let one_cc = one_c(d, p);
    let cos_one_const = d.kernel().const_(p.cos_one, vec![]);
    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_series_partial_c = d.kernel().const_(p.cos_series_partial, vec![]);

    // Peel `F`/`G`/`a`/`b` off the witness's own INFERRED type, rather than
    // reconstructing `big_f` by hand — guarantees an exact match with the
    // declared theorem's actual ascribed type.
    let ty_u = d.kernel().infer(u_conv)?;
    let (inner1, b_u) = unapp(d, ty_u);
    let (inner2, a_u) = unapp(d, inner1);
    let (inner3, g_u) = unapp(d, inner2);
    let (_, f_u) = unapp(d, inner3);
    let uconv_rate_val = d.const_app(p.uconv_rate, &[f_u, g_u, a_u, b_u, u_conv]);
    let uconv_spec_val = d.const_app(p.uconv_spec, &[f_u, g_u, a_u, b_u, u_conv]);

    let g_one = d.apply(g_u, &[one_cc]); // (cosFn | cosFnWide) one
    let target = equiv(d, p, g_one, cos_one_const);

    let predicate = converges_predicate(d, p, cos_series_partial_c, cos_one_const);
    let cos_one_converges_c = d.kernel().const_(p.cos_one_converges, vec![]);

    let minor = {
        let k1_fv = d.fresh_fvar();
        let k1 = d.kernel().fvar(k1_fv);
        let hk1_ty = d.apply(predicate, &[k1]);
        let hk1_fv = d.fresh_fvar();
        let hk1 = d.kernel().fvar(hk1_fv);

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        // --- leg 1: cosOneConverges's raw `Within` fact, bridged to `close_within`.
        let x1 = d.apply(cos_series_partial_c, &[n]);
        let hp = d.apply(hk1, &[n]);
        let (rate1, proof1) = close_within_of_within_at(d, p, x1, cos_one_const, n, k1, hp);
        let q1_rat = div_succ_at(d, p, rate1, n);
        let q1_embed = embed(d, p, q1_rat);
        let proof1_symm = close_within_symm(d, p, x1, cos_one_const, q1_embed, proof1);

        // --- leg 2: cosFnUniformConverges's own `.spec` at (n, one),
        // transported from `cosFnTerm j one` to `cosTerm j`.
        let spec_at_n = d.apply(uconv_spec_val, &[n, one_cc, hab_lo, hab_hi]);
        let rate2 = uconv_rate_val;
        let q2_rat = div_succ_at(d, p, rate2, n);
        let q2_embed = embed(d, p, q2_rat);

        let f_pt_one = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = d.const_app(p.cos_fn_term, &[j, one_cc]);
            d.lam_fv(j_fv, nat, body)
        };
        let per_j = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = cos_fn_term_one_equiv(d, p, j);
            d.lam_fv(j_fv, nat, body)
        };
        let hn = d.lemma(p.sum_range_congr, &[f_pt_one, cos_term_c, n, per_j]);
        // hn : Equiv (sum_range f_pt_one n) (sum_range cos_term_c n)
        //    = Equiv (big_f n one) x1, by defeq (big_f's own beta-reduction
        //      and cos_series_partial's own delta-unfold, respectively).

        let big_f_n_one = d.apply(f_u, &[n, one_cc]);
        let ng_one = cneg(d, p, g_one);
        let raw_diff = cadd(d, p, big_f_n_one, ng_one);
        let x1_diff = cadd(d, p, x1, ng_one);
        let refl_ng = erefl(d, p, ng_one);
        let hn2 = d.lemma(p.add_congr, &[big_f_n_one, x1, ng_one, ng_one, hn, refl_ng]);
        let abs_raw_diff = cabs(d, p, raw_diff);
        let abs_x1_diff = cabs(d, p, x1_diff);
        let habs = d.lemma(p.abs_congr, &[raw_diff, x1_diff, hn2]);
        let refl_q2 = erefl(d, p, q2_embed);
        let proof2 = d.lemma(
            p.le_congr,
            &[
                abs_raw_diff,
                abs_x1_diff,
                q2_embed,
                q2_embed,
                habs,
                refl_q2,
                spec_at_n,
            ],
        );

        // --- combine, fuse the two bounds, and close.
        let combined = combine_two_legs(
            d,
            p,
            cos_one_const,
            x1,
            g_one,
            q1_embed,
            q2_embed,
            proof1_symm,
            proof2,
        );
        // combined : le (abs (add cos_one_const (neg g_one))) (add q1_embed q2_embed)

        let radd_val = radd(d, q1_rat, q2_rat);
        let of_add_eq = d.lemma(p.of_rat_add, &[q1_rat, q2_rat]);
        let v_term = cadd(d, p, cos_one_const, ng_one);
        let abs_v = cabs(d, p, v_term);
        let refl_abs_v = erefl(d, p, abs_v);
        let bound_sum = cadd(d, p, q1_embed, q2_embed);
        let radd_embed = embed(d, p, radd_val);
        let step_a = d.lemma(
            p.le_congr,
            &[
                abs_v, abs_v, bound_sum, radd_embed, refl_abs_v, of_add_eq, combined,
            ],
        );
        // step_a : le abs_v (ofRat radd_val)

        let k3 = NatOps::add(d, rate1, rate2);
        let eq_fuse = d.lemma(p.rat.nat_div_succ_add, &[rate1, rate2, n]);
        // eq_fuse : Eq (radd q1_rat q2_rat) (natDivSucc k3 n)
        let final_bound_rat = div_succ_at(d, p, k3, n);
        let final_le = rat_eq_rewrite(d, radd_val, final_bound_rat, eq_fuse, step_a, &|d, t| {
            let target_embed = embed(d, p, t);
            cle(d, p, abs_v, target_embed)
        });
        // final_le : le abs_v (ofRat (natDivSucc k3 n))

        let per_idx = d.lam_fv(n_fv, nat, final_le);
        let v_equiv_zero = d.lemma(p.equiv_zero_of_rate, &[k3, v_term, per_idx]);
        // v_equiv_zero : Equiv v_term zero  (v_term = add cos_one_const (neg g_one))
        let equiv_e_g = equiv_of_sub_equiv_zero(d, p, cos_one_const, g_one, v_equiv_zero);
        // equiv_e_g : Equiv cos_one_const g_one
        let final_result = d.lemma(p.equiv_symm, &[cos_one_const, g_one, equiv_e_g]);
        // final_result : Equiv g_one cos_one_const

        let with_hk1 = d.lam_fv(hk1_fv, hk1_ty, final_result);
        d.lam_fv(k1_fv, nat, with_hk1)
    };

    let value = exists_elim(d, predicate, target, cos_one_converges_c, minor);

    Ok((target, value))
}

/// Admit `CReal.cosFn_one_equiv_cosOne : Equiv (cosFn one) cosOne` --
/// [`cos_limit_at_one_equiv_cos_one`] at `CReal.cosFnUniformConverges`, whose
/// interval is `[0, 1]`, so the upper range hypothesis is `le_refl one`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_fn_equiv_cos_one(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let u_conv = d.kernel().const_(p.cos_fn_uniform_converges, vec![]);
    let hab_lo = zero_le_one(d, p);
    let one_cc = one_c(d, p);
    let hab_hi = d.lemma(p.le_refl, &[one_cc]);
    let (ty, value) = cos_limit_at_one_equiv_cos_one(d, p, u_conv, hab_lo, hab_hi)?;

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_one_equiv_cos_one,
        uparams: vec![],
        ty,
        value,
    })
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

/// `Equiv (mul (mul x a) (mul y b)) (mul (mul x y) (mul a b))` -- the
/// four-factor commute-and-reassociate step [`declare_pow_mul_distrib`]'s
/// induction step needs, by a chain of `mul_assoc`/`mul_comm`/`mul_congr`:
/// `(x·a)·(y·b) = x·(a·(y·b)) = x·((a·y)·b) = x·((y·a)·b) = x·(y·(a·b)) =
/// (x·y)·(a·b)`.
fn mul_pqab_shuffle(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    let start = {
        let l = cmul(d, p, x, a);
        let r = cmul(d, p, y, b);
        cmul(d, p, l, r)
    };

    // s1 := x * (a * (y * b)), via mul_assoc(x, a, y*b).
    let yb = cmul(d, p, y, b);
    let h1 = d.lemma(p.mul_assoc, &[x, a, yb]);
    let a_yb = cmul(d, p, a, yb);
    let s1 = cmul(d, p, x, a_yb);

    // s2 := x * ((a * y) * b), via congr(symm(mul_assoc(a, y, b))) inside x*_.
    let ay = cmul(d, p, a, y);
    let ay_b = cmul(d, p, ay, b);
    let h_assoc_ayb = d.lemma(p.mul_assoc, &[a, y, b]); // Equiv ay_b a_yb
    let h2_inner = d.lemma(p.equiv_symm, &[ay_b, a_yb, h_assoc_ayb]); // Equiv a_yb ay_b
    let refl_x = d.lemma(p.equiv_refl, &[x]);
    let h2 = d.lemma(p.mul_congr, &[x, x, a_yb, ay_b, refl_x, h2_inner]);
    let s2 = cmul(d, p, x, ay_b);

    // s3 := x * ((y * a) * b), via congr(mul_comm(a, y)) inside x*(_*b).
    let ya = cmul(d, p, y, a);
    let ya_b = cmul(d, p, ya, b);
    let h3 = d.lemma(p.mul_comm, &[a, y]); // Equiv ay ya
    let refl_b = d.lemma(p.equiv_refl, &[b]);
    let h4 = d.lemma(p.mul_congr, &[ay, ya, b, b, h3, refl_b]); // Equiv ay_b ya_b
    let h5 = d.lemma(p.mul_congr, &[x, x, ay_b, ya_b, refl_x, h4]);
    let s3 = cmul(d, p, x, ya_b);

    // s4 := x * (y * (a * b)), via congr(mul_assoc(y, a, b)) inside x*_.
    let ab = cmul(d, p, a, b);
    let y_ab = cmul(d, p, y, ab);
    let h6 = d.lemma(p.mul_assoc, &[y, a, b]); // Equiv ya_b y_ab
    let h7 = d.lemma(p.mul_congr, &[x, x, ya_b, y_ab, refl_x, h6]);
    let s4 = cmul(d, p, x, y_ab);

    // mid := (x * y) * (a * b), via symm(mul_assoc(x, y, a*b)).
    let xy = cmul(d, p, x, y);
    let mid = cmul(d, p, xy, ab);
    let h8 = d.lemma(p.mul_assoc, &[x, y, ab]); // Equiv mid s4
    let h9 = d.lemma(p.equiv_symm, &[mid, s4, h8]); // Equiv s4 mid

    echain(
        d,
        p,
        start,
        &[(s1, h1), (s2, h2), (s3, h5), (s4, h7), (mid, h9)],
    )
}

/// `CReal.powMulDistrib : ∀ a b (n : Nat), Equiv (mul (pow a n) (pow b n))
/// (pow (mul a b) n)` -- power distributes over a product of bases at a
/// fixed exponent, general in `a`, `b`, `n`. Induction on `n`, mirroring
/// `power.rs::declare_pow_add`'s own shape (relying on `pow`'s
/// iota-reduction at both `zero` and `succ` rather than invoking
/// `pow_zero`/`pow_succ` explicitly): the base case is `mul_one` alone
/// (`pow _ zero` reduces to `one` regardless of base, so the goal reduces to
/// `Equiv (mul one one) one`), the step case is [`mul_pqab_shuffle`] chained
/// with the induction hypothesis congruence. This is the identity this
/// file's own "2026-08-27 update" module documentation names as missing --
/// "no power distributes over a product" -- and is genuinely general, not
/// tied to any literal ratio.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_pow_mul_distrib(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let pow_a_v = cpow(d, p, a, v);
        let pow_b_v = cpow(d, p, b, v);
        let lhs = cmul(d, p, pow_a_v, pow_b_v);
        let ab = cmul(d, p, a, b);
        let rhs = cpow(d, p, ab, v);
        equiv(d, p, lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let one_cc = one_c(d, p);
            d.lemma(p.mul_one, &[one_cc])
        },
        &|d, j, ih| {
            let pow_a_j = cpow(d, p, a, j);
            let pow_b_j = cpow(d, p, b, j);
            let ab = cmul(d, p, a, b);

            let start = {
                let l = cmul(d, p, pow_a_j, a);
                let r = cmul(d, p, pow_b_j, b);
                cmul(d, p, l, r)
            };
            let pq = cmul(d, p, pow_a_j, pow_b_j);
            let mid = cmul(d, p, pq, ab);
            let shuffle = mul_pqab_shuffle(d, p, pow_a_j, pow_b_j, a, b);

            let pow_ab_j = cpow(d, p, ab, j);
            let refl_ab = d.lemma(p.equiv_refl, &[ab]);
            let after_ih = d.lemma(p.mul_congr, &[pq, pow_ab_j, ab, ab, ih, refl_ab]);
            let end = cmul(d, p, pow_ab_j, ab);

            d.lemma(p.equiv_trans, &[start, mid, end, shuffle, after_ih])
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let inner2 = d.pi_fv(b_fv, carrier, inner);
        d.pi_fv(a_fv, carrier, inner2)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let inner2 = d.lam_fv(b_fv, carrier, inner);
        d.lam_fv(a_fv, carrier, inner2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_mul_distrib,
        uparams: vec![],
        ty,
        value,
    })
}

/// Peel `Eq Rat a b`'s trailing `a`, `b` off an inferred `Eq`-type, without
/// hand-reconstructing the `normalize`/`Int.mul`/`Nat.mul` terms a `Rat`
/// lemma application actually produces -- mirrors [`declare_cos_fn`]'s own
/// `unapp`-based extraction of `UniformConvergesOn`'s `G`.
fn req_sides(d: &mut IntDev<'_>, proof: ExprId) -> Result<(ExprId, ExprId), KernelError> {
    let ty = d.kernel().infer(proof)?;
    Ok(two_sides(d, ty))
}

/// Peel a two-argument application's trailing `a`, `b` off `ty` (either `Eq
/// Rat a b`'s inner `App(App(Eq{u},Rat),a)` spine, or `Equiv a b` directly --
/// both need exactly two [`unapp`] peels to reach `(a, b)`).
fn two_sides(d: &mut IntDev<'_>, ty: ExprId) -> (ExprId, ExprId) {
    let (inner, b) = unapp(d, ty);
    let (_, a) = unapp(d, inner);
    (a, b)
}

/// `Rat.natDivSucc 8 4` = `8/5` -- the wide-cosine domain bound `R`. `R :=
/// 8/5` clears cosine's first zero (`≈ 1.5708`); combined ratio `(R/2)² =
/// 16/25`, matching `geometric.rs::ratio_16_over_25_witnesses`.
fn r_domain_rat(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let n8 = d.num(8);
    let n4 = d.num(4);
    d.const_app(rat.nat_div_succ, &[n8, n4])
}

/// `CReal.ofRat (Rat.natDivSucc 8 4)` -- the wide-cosine domain bound `R :=
/// 8/5` as a `CReal`.
fn r_domain(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rr = r_domain_rat(d, p);
    embed(d, p, rr)
}

/// `Equiv (embed a) (embed b)`, from `Eq Rat a b` -- congruence of `embed`
/// along a `Rat`-level rewrite. Reproduced verbatim from `geometric.rs`'s
/// own private `embed_eq_to_equiv` (this development's established
/// convention: reproduce a sibling module's private helper rather than
/// widen its visibility).
fn embed_eq_to_equiv_here(
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

/// `Equiv (mul (mul half R) (mul half R)) (ofRat (natDivSucc 16 24))`, where
/// `R := ofRat (natDivSucc 8 4)` -- the `Rat`-arithmetic bridge this file's
/// own "2026-08-27 update" module documentation names as missing: `(1/2 ·
/// 8/5)² = 16/25`.
///
/// Built via `Rat.normalize_mul_normalize` (fusing `half_rat * R_rat` into a
/// single `normalize 8 10`, then squaring that into `normalize 64 100`) and
/// `Rat.normalize_congr` (reducing `8/10` to `4/5` BEFORE squaring, so the
/// square lands directly on `normalize 16 25` -- `natDivSucc 16 24`'s own
/// literal form -- with no further reduction needed): `1/2 · 8/5 = 8/10 =
/// 4/5`, `(4/5)·(4/5) = 16/25`. Every intermediate representative is read
/// back off the actual lemma applications via [`req_sides`], never
/// hand-reconstructed.
fn half_r_squared_eq_16_over_25(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<ExprId, KernelError> {
    let rat = p.rat;

    let half_rat = super::exponential::half_rat(d, p);
    let r_rat = r_domain_rat(d, p);

    // step0 : Eq Rat (Rat.mul half_rat R_rat) (normalize (1*8) (2*5) _).
    let one_a = d.num(1);
    let one_int = d.of_nat(one_a);
    let one_b = d.num(1);
    let succ1 = d.succ(one_b);
    let one_c_nat = d.num(1);
    let h_a = one_le_succ(d, one_c_nat);
    let eight_a = d.num(8);
    let eight_int = d.of_nat(eight_a);
    let four_a = d.num(4);
    let succ4 = d.succ(four_a);
    let four_b = d.num(4);
    let h_b = one_le_succ(d, four_b);
    let step0 = d.lemma(
        rat.normalize_mul_normalize,
        &[one_int, succ1, h_a, eight_int, succ4, h_b],
    );
    let (_, q0_raw) = req_sides(d, step0)?;

    // step1 : Eq Rat (normalize 8 10 _) (normalize 4 5 _), via
    // normalize_congr at the cross-multiplication identity 8*5 = 4*10.
    let n8 = d.num(8);
    let n1 = d.of_nat(n8);
    let n9 = d.num(9);
    let e1 = d.succ(n9); // 10
    let h1 = one_le_succ(d, n9);
    let n4 = d.num(4);
    let n2 = d.of_nat(n4);
    let n4b = d.num(4);
    let e2 = d.succ(n4b); // 5
    let n4c = d.num(4);
    let h2 = one_le_succ(d, n4c);
    let hyp = {
        let e2_z = d.of_nat(e2);
        let lhs = d.imul(n1, e2_z);
        d.irefl(lhs)
    };
    let step1 = d.lemma(rat.normalize_congr, &[n1, e1, h1, n2, e2, h2, hyp]);
    let (_, q1) = req_sides(d, step1)?;

    // half_r_eq : Eq Rat (Rat.mul half_rat R_rat) (normalize 4 5 _) -- chain
    // step0 then step1 (via q0_raw, which is defeq to step1's own LHS since
    // both compute `1*8 = 8`, `2*5 = 10`).
    let half_r_eq = {
        let target_lhs = rmul_here(d, half_rat, r_rat);
        let motive_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            crate::rat_prelude::ops::req(d, target_lhs, x)
        };
        rat_rewrite(d, q0_raw, q1, step1, step0, &motive_at)
    };

    // step2 : Eq Rat (Rat.mul (normalize 4 5 _) (normalize 4 5 _))
    // (normalize (4*4) (5*5) _) -- literally `normalize 16 25 _`, matching
    // `natDivSucc 16 24`'s own unfolding, up to computation.
    let step2 = d.lemma(rat.normalize_mul_normalize, &[n2, e2, h2, n2, e2, h2]);
    let (q1q1_raw, q2) = req_sides(d, step2)?;

    // y_eq : Equiv (mul half R) (embed (normalize 4 5 _)).
    let half_c = super::exponential::half(d, p);
    let r_c = r_domain(d, p);
    let y = cmul(d, p, half_c, r_c);
    let y_eq = {
        let step_of_rat = d.lemma(p.of_rat_mul, &[half_rat, r_rat]); // Equiv y (embed(Rat.mul half_rat r_rat))
        let half_r_raw = rmul_here(d, half_rat, r_rat);
        let embed_raw = embed(d, p, half_r_raw);
        let embed_q1 = embed(d, p, q1);
        let bridge = embed_eq_to_equiv_here(d, p, half_r_raw, q1, half_r_eq);
        d.lemma(
            p.equiv_trans,
            &[y, embed_raw, embed_q1, step_of_rat, bridge],
        )
    };

    // yy_eq : Equiv (mul y y) (embed q2).
    let yy = cmul(d, p, y, y);
    let embed_q1_c = embed(d, p, q1);
    let yy_step1 = d.lemma(p.mul_congr, &[y, embed_q1_c, y, embed_q1_c, y_eq, y_eq]);
    let mul_embed_q1 = cmul(d, p, embed_q1_c, embed_q1_c);
    let yy_step2 = d.lemma(p.of_rat_mul, &[q1, q1]); // Equiv (mul embed_q1 embed_q1) (embed q1q1_raw)
    let embed_mul_q1q1 = embed(d, p, q1q1_raw);
    let step2_bridge = embed_eq_to_equiv_here(d, p, q1q1_raw, q2, step2);
    let embed_q2 = embed(d, p, q2);
    let chain1 = d.lemma(
        p.equiv_trans,
        &[yy, mul_embed_q1, embed_mul_q1q1, yy_step1, yy_step2],
    );
    let yy_eq = d.lemma(
        p.equiv_trans,
        &[yy, embed_mul_q1q1, embed_q2, chain1, step2_bridge],
    );

    // `yy_eq`'s inferred type is `Equiv (mul y y) (embed q2)`, with `q2`
    // computing to `normalize 16 25 _` -- defeq to `natDivSucc 16 24`'s own
    // unfolding (proof-irrelevant in the witness), which is what
    // [`declare_cos_fn_wide`] ascribes this against.
    Ok(yy_eq)
}

/// `Rat.mul a b`, local to this file (mirrors `rat_prelude::ops::rmul`,
/// re-exposed here so this file's own helpers read uniformly).
fn rmul_here(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    crate::rat_prelude::ops::rmul(d, a, b)
}

/// `Eq Rat` transport: from `h : Eq Rat p q` and a proof of `motive(p)`,
/// derive `motive(q)`. Thin wrapper over `rat_prelude::ops::rtransport` with
/// the motive built the same way `rat_eq_rewrite` builds it.
fn rat_rewrite(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    proof: ExprId,
    motive: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    crate::rat_prelude::ops::rat_eq_rewrite(d, a, b, h, proof, motive)
}

/// Admit the wider-cosine PROGRESS pieces: the pointwise domination bound
/// past `[0, 1]` and the ratio-`16/25` dominating series' raw Cauchy
/// witness, plus the general `pow` distribution identity. Does NOT apply
/// `weierstrassMTest` -- see the module documentation's "2026-08-27 update"
/// section for exactly why, and what remains.
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
    declare_cos_dominant_16_over_25_cauchy_body(d, p)?;
    declare_pow_mul_distrib(d, p)
}

/// `Equiv (mul (expDominant (add j j)) (pow R (add j j))) (cosDominant16Over25
/// j)`, where `R := ofRat (natDivSucc 8 4)` -- the bridge
/// [`declare_cos_fn_wide`]'s `hdom0` needs, connecting
/// [`declare_cos_fn_term_abs_le_wide`]'s raw bound to
/// [`declare_cos_dominant_16_over_25`]'s exact dominating-series shape. Two
/// applications of [`declare_pow_mul_distrib`] (once directly at exponent
/// `add j j` to fuse `pow half(2j) · pow R(2j)`, once more -- after
/// `pow_add` splits that same doubled exponent -- to square the fused base)
/// plus [`half_r_squared_eq_16_over_25`] to identify the squared base with
/// the literal ratio `16/25`.
fn wide_bound_bridge(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    j: ExprId,
) -> Result<ExprId, KernelError> {
    let half_c = super::exponential::half(d, p);
    let r_c = r_domain(d, p);
    let two_c = two(d, p);
    let jj = d.add(j, j);

    let pow_half_jj = cpow(d, p, half_c, jj);
    let pow_r_jj = cpow(d, p, r_c, jj);
    let start = {
        let ed_jj = cmul(d, p, two_c, pow_half_jj);
        cmul(d, p, ed_jj, pow_r_jj)
    };

    // s1 := two * (pow_half_jj * pow_r_jj), via mul_assoc.
    let inner_hr = cmul(d, p, pow_half_jj, pow_r_jj);
    let s1 = cmul(d, p, two_c, inner_hr);
    let h1 = d.lemma(p.mul_assoc, &[two_c, pow_half_jj, pow_r_jj]);

    let y = cmul(d, p, half_c, r_c);
    let refl_two = d.lemma(p.equiv_refl, &[two_c]);

    // s2 := two * (pow y jj), via pow_mul_distrib(half, R, jj) inside two*_.
    let distrib1 = d.lemma(p.pow_mul_distrib, &[half_c, r_c, jj]);
    let pow_y_jj = cpow(d, p, y, jj);
    let h2 = d.lemma(
        p.mul_congr,
        &[two_c, two_c, inner_hr, pow_y_jj, refl_two, distrib1],
    );
    let s2 = cmul(d, p, two_c, pow_y_jj);

    // s3 := two * ((pow y j) * (pow y j)), via pow_add(y, j, j) inside two*_.
    let pow_y_j = cpow(d, p, y, j);
    let mul_yy_j = cmul(d, p, pow_y_j, pow_y_j);
    let h3_inner = d.lemma(p.pow_add, &[y, j, j]);
    let h3 = d.lemma(
        p.mul_congr,
        &[two_c, two_c, pow_y_jj, mul_yy_j, refl_two, h3_inner],
    );
    let s3 = cmul(d, p, two_c, mul_yy_j);

    // s4 := two * (pow (mul y y) j), via pow_mul_distrib(y, y, j) inside two*_.
    let yy = cmul(d, p, y, y);
    let pow_yy_j = cpow(d, p, yy, j);
    let distrib2 = d.lemma(p.pow_mul_distrib, &[y, y, j]);
    let h4 = d.lemma(
        p.mul_congr,
        &[two_c, two_c, mul_yy_j, pow_yy_j, refl_two, distrib2],
    );
    let s4 = cmul(d, p, two_c, pow_yy_j);

    // target := two * (pow embed_q2 j), rewriting the base via
    // half_r_squared_eq_16_over_25 (`Equiv yy (embed q2)`, `q2` defeq the
    // literal `natDivSucc 16 24`).
    let yy_eq = half_r_squared_eq_16_over_25(d, p)?;
    let yy_ty = d.kernel().infer(yy_eq)?;
    let (_, embed_q2) = two_sides(d, yy_ty);
    let pow_target_j = cpow(d, p, embed_q2, j);
    let h5 = d.lemma(p.pow_congr, &[yy, embed_q2, yy_eq, j]);
    let h5c = d.lemma(
        p.mul_congr,
        &[two_c, two_c, pow_yy_j, pow_target_j, refl_two, h5],
    );
    let target = cmul(d, p, two_c, pow_target_j);

    Ok(echain(
        d,
        p,
        start,
        &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (target, h5c)],
    ))
}

/// Admit `CReal.cosFnWide` and `CReal.cosFnWideUniformConverges`, mirroring
/// [`declare_cos_fn`] but at domain `[0, R]` (`R := ofRat (natDivSucc 8 4) =
/// 8/5`, clearing cosine's first zero) with dominating series
/// `cosDominant16Over25` rather than `expDominant`. Run after
/// [`declare_cos_fn_family`] and [`declare_cos_fn_wide_progress`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_fn_wide(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let r_c = r_domain(d, p);

    let f0 = d.kernel().const_(p.cos_fn_term, vec![]);
    let mseq0 = d.kernel().const_(p.cos_dominant_16_over_25, vec![]);

    // hab0 : le zero R.
    let hab0 = {
        let rat = p.rat;
        let zero_r = crate::rat_prelude::ops::rzero(d, rat);
        let r_rat = r_domain_rat(d, p);
        let n8 = d.num(8);
        let n4 = d.num(4);
        let nn = d.lemma(rat.zero_le_nat_div_succ, &[n8, n4]);
        d.lemma(p.of_rat_le, &[zero_r, r_rat, nn])
    };

    // hcong0 : forall j p q, Equiv p q -> Equiv (f0 j p) (f0 j q).
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

    let (k_g, hcauchy0) = cos_dominant_16_over_25_cauchy_body_concrete(d, p);

    // hdom0 : forall j pt, le zero pt -> le pt R -> le (abs (f0 j pt)) (mseq0 j).
    let hdom0 = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxr_fv = d.fresh_fvar();
        let hxr = d.kernel().fvar(hxr_fv);

        let raw_bound = d.lemma(p.cos_fn_term_abs_le_wide, &[pt, hax, r_c, hxr, j]);

        let bridge = wide_bound_bridge(d, p, j)?;

        let abs_cft = {
            let cft = d.const_app(p.cos_fn_term, &[j, pt]);
            cabs(d, p, cft)
        };
        let refl_lhs = d.lemma(p.equiv_refl, &[abs_cft]);
        let bound = {
            let ed = d.kernel().const_(p.exp_dominant, vec![]);
            let two_j = d.add(j, j);
            let ed_2j = d.apply(ed, &[two_j]);
            let pow_r_2j = cpow(d, p, r_c, two_j);
            cmul(d, p, ed_2j, pow_r_2j)
        };
        let mseq0_j = d.apply(mseq0, &[j]);
        let transported = d.lemma(
            p.le_congr,
            &[
                abs_cft, abs_cft, bound, mseq0_j, refl_lhs, bridge, raw_bound,
            ],
        );

        let hxr_ty = cle(d, p, pt, r_c);
        let hax_ty = cle(d, p, zero_c, pt);
        let with_hxr = d.lam_fv(hxr_fv, hxr_ty, transported);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxr);
        let with_pt = d.lam_fv(pt_fv, carrier, with_hax);
        d.lam_fv(j_fv, nat, with_pt)
    };

    let u0 = d.lemma(
        p.weierstrass_m_test,
        &[f0, mseq0, zero_c, r_c, hab0, hcong0, k_g, hdom0, hcauchy0],
    );
    let ty0 = d.kernel().infer(u0)?;

    let (inner1, _b0) = unapp(d, ty0);
    let (inner2, _a0) = unapp(d, inner1);
    let (_inner3, g0) = unapp(d, inner2);

    let cos_fn_wide_ty = d.arrow(carrier, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cos_fn_wide,
        uparams: vec![],
        ty: cos_fn_wide_ty,
        value: g0,
        hint: ReducibilityHint::Regular(COS_FN_TERM_HEIGHT + 3),
    })?;

    let big_f = cos_fn_partial_sums_fn(d, p, carrier, nat);
    let cos_fn_wide_c = d.kernel().const_(p.cos_fn_wide, vec![]);
    let ty = d.const_app(p.uniform_converges_on, &[big_f, cos_fn_wide_c, zero_c, r_c]);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_wide_uniform_converges,
        uparams: vec![],
        ty,
        value: u0,
    })
}

// ============================================================================
// `CReal.cosFnWideUniformlyContinuous`
// ============================================================================
//
// Route: `CReal.uniform_limit_uniformly_continuous` applied at
// `CReal.cosFnWideUniformConverges`. Its second hypothesis, `∀ n,
// UniformlyContinuousOn (F n) zero R`, is built by induction on `n`
// (`Nat.rec` at `level_one`, [`induct_ty`], since `UniformlyContinuousOn` is
// `Type`-valued -- see `uniform_continuity.rs`'s own module documentation).
// The step case needs `UniformlyContinuousOn (cosFnTerm n ·) zero R` for the
// CURRENT induction variable, which is [`cos_fn_term_uc`] -- itself needing
// `pow` uniform continuity at a symbolic exponent, a SEPARATE (nested)
// induction over the base, built once up front and applied at `Nat.add n n`.
// Every `BoundedOn` hypothesis either induction needs comes from
// `CReal.bounded_of_uniformly_continuous` ([`bounded_via_uc`]), never
// hand-derived -- both `CReal.bounded_on_mul` and this generic route exist
// in the tree; the generic route needs no per-shape bound computation.

/// `fun pt => pow pt m` -- the base-varying dual of [`pow_fn_local`] (`fun n
/// => pow x n`, exponent-varying). Needed for the `pow` uniform continuity
/// induction below, which is over the BASE at a fixed (possibly symbolic)
/// exponent `m`.
fn pow_base_fn(d: &mut IntDev<'_>, p: CRealPrelude, carrier: ExprId, m: ExprId) -> ExprId {
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let body = cpow(d, p, pt, m);
    d.lam_fv(pt_fv, carrier, body)
}

/// `le zero R`, `R := ofRat (natDivSucc 8 4) = 8/5` -- reproduced verbatim
/// from [`declare_cos_fn_wide`]'s own `hab0` block (needed independently
/// here, since this function's induction does not call that one).
fn hab_zero_r(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let zero_r = crate::rat_prelude::ops::rzero(d, rat);
    let r_rat = r_domain_rat(d, p);
    let n8 = d.num(8);
    let n4 = d.num(4);
    let nn = d.lemma(rat.zero_le_nat_div_succ, &[n8, n4]);
    d.lemma(p.of_rat_le, &[zero_r, r_rat, nn])
}

/// [`crate::nat_prelude::NatOps::induct`]'s own body, but at universe
/// `level_one` rather than the trait method's hardcoded `level_zero` --
/// needed here because `UniformlyContinuousOn` is `Type`-valued, so a
/// `Nat`-indexed FAMILY of its proofs needs `Nat.rec`'s large-elimination
/// form, exactly the way `uniform_continuity.rs`'s own `declare_carrier`/
/// `declare_projections` (`uc_rec` at `level_one`) already need for the
/// SAME reason.
fn induct_ty(
    d: &mut IntDev<'_>,
    motive: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    base: &dyn Fn(&mut IntDev<'_>) -> ExprId,
    step: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
    target: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let motive_lam = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = motive(d, x);
        d.lam_fv(x_fv, nat, body)
    };
    let base_term = base(d);
    let step_term = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let hyp_ty = motive(d, j);
        let body = step(d, j, ih);
        let inner = d.lam_fv(ih_fv, hyp_ty, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let one = d.level_one();
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[motive_lam, base_term, step_term, target])
}

/// Peel a `Kernel::fvar`-built [`ExprId`] back to its raw id. Used only to
/// re-register an induction's own bound `j`/`ih` as free-in-context locals
/// for [`bounded_via_uc`]'s `infer_in` call -- these ids were minted by this
/// same file's own `d.fresh_fvar()`/`d.kernel().fvar(..)` calls, never
/// parsed from anything untrusted.
fn fvar_id(d: &mut IntDev<'_>, e: ExprId) -> u64 {
    match d.kernel().expr_node(e).clone() {
        ExprNode::FVar(id) => id,
        other => panic!("expected a free variable, found {other:?}"),
    }
}

/// `CReal.bounded_of_uniformly_continuous` applied at `f, a, b, huc, hab`,
/// with its computed `K` read back via [`unapp`] rather than hand-derived --
/// this file's own established convention for reading a lemma application's
/// own output back off itself (see e.g. [`declare_cos_fn_wide`]'s `G`
/// extraction). Returns `(K, proof)`, `proof : BoundedOn f a b K`.
///
/// `free_vars` lists every `(fvar id, type)` pair the assembled application
/// mentions but does not yet bind (an enclosing induction's own `j`/`ih`,
/// still open at the point this is called) -- `Kernel::infer` alone uses a
/// FRESH, empty context and rejects any such term as `UnboundFVar`, so
/// these must be registered into a [`LocalContext`] via `infer_in` instead.
fn bounded_via_uc(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    huc: ExprId,
    hab: ExprId,
    free_vars: &[(u64, ExprId)],
) -> (ExprId, ExprId) {
    let proof = d.lemma(p.bounded_of_uniformly_continuous, &[f, a, b, huc, hab]);
    let anon = d.anon_name();
    let mut ctx = LocalContext::new();
    for &(fvar, ty) in free_vars {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }
    let ty = d
        .kernel()
        .infer_in(proof, &mut ctx)
        .expect("bounded_of_uniformly_continuous application must infer a type");
    let (_inner, k) = unapp(d, ty);
    (k, proof)
}

/// `UniformlyContinuousOn (fun pt => cosFnTerm k pt) zero R`, for symbolic
/// `k`. Built from `pow_uc : ∀ m, UniformlyContinuousOn (fun pt => pow pt m)
/// zero R` (this file's own nested induction, threaded in already built)
/// applied at `m := Nat.add k k`, combined with the constant function `fun
/// _ => cosTerm k` via `CReal.uniformly_continuous_mul`. `cosFnTerm k x ≡
/// mul (cosTerm k) (pow x (Nat.add k k))` is a `Definition` unfold + beta
/// away from this function's own conclusion, so no congruence lemma is
/// needed -- the kernel's own defeq check bridges the two, this file's
/// "computed, not extracted" convention.
fn cos_fn_term_uc(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    nat: ExprId,
    zero_c: ExprId,
    r_c: ExprId,
    hab0: ExprId,
    pow_uc: ExprId,
    k: ExprId,
) -> ExprId {
    let k_id = fvar_id(d, k);
    let free_k = [(k_id, nat)];

    let two_k = d.add(k, k);
    let pow_2k_fn = pow_base_fn(d, p, carrier, two_k);
    let huc_pow2k = d.apply(pow_uc, &[two_k]);

    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_term_k = d.apply(cos_term_c, &[k]);
    let const_fn = {
        let pt_fv = d.fresh_fvar();
        d.lam_fv(pt_fv, carrier, cos_term_k)
    };
    let huc_const = d.lemma(p.uniformly_continuous_const, &[cos_term_k, zero_c, r_c]);

    let (k1, hb1) = bounded_via_uc(d, p, const_fn, zero_c, r_c, huc_const, hab0, &free_k);
    let (k2, hb2) = bounded_via_uc(d, p, pow_2k_fn, zero_c, r_c, huc_pow2k, hab0, &free_k);

    d.lemma(
        p.uniformly_continuous_mul,
        &[
            const_fn, pow_2k_fn, zero_c, r_c, huc_const, huc_pow2k, k1, k2, hb1, hb2,
        ],
    )
}

/// Admit `CReal.cosFnWideUniformlyContinuous : UniformlyContinuousOn
/// cosFnWide zero R` -- the hypothesis `creal/ivt.rs`'s `ivt_approx` needs
/// to reach an approximate root of `cosFnWide` at all. See this file's own
/// module documentation, "What π still needs".
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_fn_wide_uniformly_continuous(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let r_c = r_domain(d, p);
    let hab0 = hab_zero_r(d, p);

    // `pow_uc : ∀ m, UniformlyContinuousOn (fun pt => pow pt m) zero R` --
    // the nested induction over `pow`'s base, shared with
    // [`declare_sin_fn_uniformly_continuous`] and the derivative section's
    // two Skolem bound builders rather than reproduced per call site.
    let pow_uc = pow_uc_fn(d, p, carrier, nat, zero_c, r_c, hab0);

    // --- outer induction: partial-sum uniform continuity, over `n` -------
    let big_f = cos_fn_partial_sums_fn(d, p, carrier, nat);

    let sum_motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let fv = d.apply(big_f, &[v]);
        d.const_app(p.uniformly_continuous_on, &[fv, zero_c, r_c])
    };
    let sum_base = |d: &mut IntDev<'_>| -> ExprId {
        d.lemma(p.uniformly_continuous_const, &[zero_c, zero_c, r_c])
    };
    let sum_step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let sum_j_fn = {
            let pt_fv = d.fresh_fvar();
            let pt = d.kernel().fvar(pt_fv);
            let f_pt = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let body = d.const_app(p.cos_fn_term, &[k, pt]);
                d.lam_fv(k_fv, nat, body)
            };
            let body = d.const_app(p.sum_range, &[f_pt, j]);
            d.lam_fv(pt_fv, carrier, body)
        };
        let term_j_fn = {
            let pt_fv = d.fresh_fvar();
            let pt = d.kernel().fvar(pt_fv);
            let body = d.const_app(p.cos_fn_term, &[j, pt]);
            d.lam_fv(pt_fv, carrier, body)
        };
        let term_j_uc = cos_fn_term_uc(d, p, carrier, nat, zero_c, r_c, hab0, pow_uc, j);
        d.lemma(
            p.uniformly_continuous_add,
            &[sum_j_fn, term_j_fn, zero_c, r_c, ih, term_j_uc],
        )
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hc_at_n = induct_ty(d, &sum_motive, &sum_base, &sum_step, n);
    let hc = d.lam_fv(n_fv, nat, hc_at_n);
    // hc : ∀ n, UniformlyContinuousOn (App(big_f, n)) zero R.

    let g0 = d.kernel().const_(p.cos_fn_wide, vec![]);
    let hu = d.kernel().const_(p.cos_fn_wide_uniform_converges, vec![]);

    let value = d.lemma(
        p.uniform_limit_uniformly_continuous,
        &[big_f, g0, zero_c, r_c, hu, hc],
    );
    let ty = d.const_app(p.uniformly_continuous_on, &[g0, zero_c, r_c]);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_wide_uniformly_continuous,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// `CReal.cosFnWide` AT `x = 1` — the left endpoint of the sub-interval a π
// construction has to run `CReal.ivt_exact_root` over.
//
// `ivt_exact_root` wants a derivative bounded strictly BELOW by a positive
// constant. Cosine decreases, so the function to feed it is `fun x => neg
// (cosFnWide x)`, whose derivative is `sinFn` -- and `sin 0 = 0`, so the
// positive lower bound is unavailable on `[0, 8/5]` and the interval has to
// start away from `0`. `[1, 8/5]` is the choice that still encloses cosine's
// first zero (`≈ 1.5708`), and its left endpoint needs `0 ≤ cos 1`.
//
// **`CReal.cosOne_nonneg` is NOT that fact**, and the gap is the whole point
// of this section: `cosOne` is `creal/trig.rs`'s single CONSTANT (the limit
// of `sumRange cosTerm`), while `cosFnWide` is a FUNCTION obtained as
// `weierstrassMTest`'s uniform limit `G`. Nothing relates them until
// something proves `Equiv (cosFnWide one) cosOne`, and
// `CReal.cosFn_one_equiv_cosOne` proves it only for the NARROW `cosFn` on
// `[0, 1]`, a different declaration.
// ============================================================================

/// `le one R`, `R := ofRat (Rat.natDivSucc 8 4) = 8/5` -- the upper range
/// hypothesis `cosFnWideUniformConverges`'s `.spec` needs at `x := one`, and
/// [`hab_zero_r`]'s companion at the other end.
///
/// Route, and it costs nothing beyond one `Rat.normalize_congr` (the CHEAP
/// kind of `Rat` fact -- an `Eq` between two `normalize`s, per
/// `docs/plan/status/166-cos-deriv2.md`'s pricing note):
///
/// 1. `Rat.natDivSucc_le_add_left 5 3 4 : Rat.le (natDivSucc 5 4)
///    (natDivSucc (Nat.add 5 3) 4)`. `Nat.add 5 3` is literally the unary
///    numeral `8`, so this IS `5/5 ≤ 8/5` at the target's own denominator --
///    no index arithmetic, no cross-multiplication battery.
/// 2. `natDivSucc 5 4` is `Rat.one`. Proved WITHOUT touching `Nat.gcd` (which
///    does not unfold by ι even on literals), by exactly the route
///    `creal/trig.rs::exp_term_lit_eq_one` already uses for `expTerm 0 = 1`:
///    `Rat.self_normalize` at `q := Rat.one` names `Rat.one` as a
///    `normalize (num one) (den one) _`, `num`/`den` of a `Rat.mk`-built
///    value ι-reduce to `ofNat 1`/`1`, and `Rat.normalize_congr` bridges
///    `normalize (ofNat 5) 5 _` to it on the cross-multiplication
///    `5 · 1 = 1 · 5`, whose two sides are the SAME `Int.ofNat 5` after
///    `Nat.mul` computes -- so `Eq.refl` closes it.
/// 3. `CReal.of_rat_le` lifts the `Rat` order to `CReal`; the result reads as
///    `le one R` because `CReal.one` is *defined* as `ofRat Rat.one`
///    (`creal.rs::declare_constants`), so no `Equiv` bridge is needed either.
pub(super) fn one_le_r_domain(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let n3 = d.num(3);
    let n4 = d.num(4);
    let n5 = d.num(5);

    // `Rat.natDivSucc 5 4`, spelled the way its own definition unfolds.
    let five_int = d.of_nat(n5);
    let den5 = d.succ(n4);
    let h5 = one_le_succ(d, n4);
    let five_fifths = normalize(d, five_int, den5, h5);

    // `Rat.one`, spelled the way `self_normalize`'s own conclusion does.
    let rat_one_c = d.kernel().const_(rat.one, vec![]);
    let num_one = crate::rat_prelude::ops::num(d, rat_one_c);
    let den_one = crate::rat_prelude::ops::den(d, rat_one_c);
    let pos_one = crate::rat_prelude::ops::den_pos(d, rat_one_c);
    let renorm_one = normalize(d, num_one, den_one, pos_one);

    // `Eq Int (5 · ofNat (den one)) (num one · ofNat 5)` -- both sides reduce
    // to `Int.ofNat 5`, so reflexivity at the left one type-checks against it.
    let of_den_one = d.of_nat(den_one);
    let cross_left = d.imul(five_int, of_den_one);
    let cross = d.irefl(cross_left);
    let congr = d.lemma(
        rat.normalize_congr,
        &[five_int, den5, h5, num_one, den_one, pos_one, cross],
    );
    let self_norm = d.lemma(rat.self_normalize, &[rat_one_c]);
    let five_eq_one = rtrans(d, five_fifths, renorm_one, rat_one_c, congr, self_norm);

    let widened = d.lemma(rat.nat_div_succ_le_add_left, &[n5, n3, n4]);
    let r_rat = r_domain_rat(d, p);
    let one_le_r_rat = rat_eq_rewrite(d, five_fifths, rat_one_c, five_eq_one, widened, &|d, t| {
        crate::rat_prelude::ops::rle(d, rat, t, r_rat)
    });
    d.lemma(p.of_rat_le, &[rat_one_c, r_rat, one_le_r_rat])
}

/// `CReal.cosFnWide_one_equiv_cosOne : Equiv (cosFnWide one) cosOne` and
/// `CReal.cosFnWide_one_nonneg : le zero (cosFnWide one)`.
///
/// The first is [`cos_limit_at_one_equiv_cos_one`] at
/// `CReal.cosFnWideUniformConverges` -- the SAME body
/// [`declare_cos_fn_equiv_cos_one`] runs, differing only in the two range
/// hypotheses `[0, 8/5]` demands ([`zero_le_one`] and [`one_le_r_domain`]
/// where the narrow one uses `zero_le_one` and `le_refl one`). The second is
/// `CReal.cosOne_nonneg` transported across it by `le_congr`.
///
/// **What this is and is not.** `cos 1 ≈ 0.5403 > 0` is the FIRST of the
/// three numeric obligations a π-via-`ivt_exact_root` construction carries;
/// the other two -- `cos (8/5) < 0` and a uniform positive lower bound on
/// `sinFn` over `[1, 8/5]` -- are NOT proved here or anywhere in this tree,
/// and `docs/plan/status/169-pi.md` sizes both. Nothing in this section
/// constructs `CReal.pi`, and nothing here asserts a root exists.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_fn_wide_at_one(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let u_conv = d.kernel().const_(p.cos_fn_wide_uniform_converges, vec![]);
    let hab_lo = zero_le_one(d, p);
    let hab_hi = one_le_r_domain(d, p);
    let (ty, value) = cos_limit_at_one_equiv_cos_one(d, p, u_conv, hab_lo, hab_hi)?;
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_wide_one_equiv_cos_one,
        uparams: vec![],
        ty,
        value,
    })?;

    declare_cos_fn_wide_one_nonneg(d, p)
}

/// `CReal.cosFnWide_one_nonneg : le zero (cosFnWide one)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_fn_wide_one_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let zero_c = czero(d, p);
    let one_cc = one_c(d, p);
    let cos_one_const = d.kernel().const_(p.cos_one, vec![]);
    let wide = d.kernel().const_(p.cos_fn_wide, vec![]);
    let wide_one = d.apply(wide, &[one_cc]);

    // `Equiv (cosFnWide one) cosOne`, so the `le_congr` slot -- which rewrites
    // LEFT to RIGHT -- needs it the other way round.
    let equiv_fwd = d.kernel().const_(p.cos_fn_wide_one_equiv_cos_one, vec![]);
    let equiv_back = d.lemma(p.equiv_symm, &[wide_one, cos_one_const, equiv_fwd]);
    let refl_zero = erefl(d, p, zero_c);
    let base = d.lemma(p.cos_one_nonneg, &[]);
    let value = d.lemma(
        p.le_congr,
        &[
            zero_c,
            zero_c,
            cos_one_const,
            wide_one,
            refl_zero,
            equiv_back,
            base,
        ],
    );
    let ty = cle(d, p, zero_c, wide_one);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_wide_one_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.hasDerivativeOn_restrict : ∀ F F' a b a' b', HasDerivativeOn F F' a
/// b → le a a' → le a' b' → le b' b → HasDerivativeOn F F' a' b'` -- the
/// sub-interval restriction of a derivative witness.
///
/// **Exactly `CReal.uniformlyContinuousOn_restrict`'s construction, one
/// parameter over.** `HasDerivativeOn`'s `spec` takes the four range
/// hypotheses `le a x`, `le x b`, `le a y`, `le y b` (verbatim
/// `UniformlyContinuousOn`'s own, per `creal.rs`'s field doc), so `a ≤ a' ≤
/// x` and `y ≤ b' ≤ b` compose through `CReal.le_trans` to the original
/// witness's hypotheses and its `spec` is reused at every `(e, x, y)`. The
/// `modulus` field is carried over unchanged, so no estimate is re-derived
/// and no rate moves. The signature deliberately mirrors the uniform-
/// continuity restriction's, including its `le a' b'` argument, so the two
/// are callable side by side on one interval pair.
///
/// **Why it is declared from `creal/trig_fn.rs`.** It belongs in
/// `creal/derivative.rs` beside `hasDerivative_neg`, which is another lane's
/// file -- the same parking `CReal.natDivSuccStepLe` already documents. It is
/// general in `F`, `F'` and both interval pairs, not tied to cosine.
///
/// A π construction needs it because `CReal.cosFnWideHasDerivative` is stated
/// on `[0, 8/5]` while `CReal.ivt_exact_root` has to be applied on a
/// sub-interval bounded away from `0` (`sin 0 = 0`, so the uniformly positive
/// derivative bound is unavailable at the left end of the full domain).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_has_derivative_on_restrict(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let a2_fv = d.fresh_fvar();
    let a2 = d.kernel().fvar(a2_fv);
    let b2_fv = d.fresh_fvar();
    let b2 = d.kernel().fvar(b2_fv);

    let hf_ty = hd_ty(d, p, f, fp, a, b);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hlo_ty = cle(d, p, a, a2);
    let hlo_fv = d.fresh_fvar();
    let hlo = d.kernel().fvar(hlo_fv);
    let hmid_ty = cle(d, p, a2, b2);
    let hmid_fv = d.fresh_fvar();
    let hhi_ty = cle(d, p, b2, b);
    let hhi_fv = d.fresh_fvar();
    let hhi = d.kernel().fvar(hhi_fv);

    // The restricted witness carries the ORIGINAL modulus, unchanged.
    let modulus = d.const_app(p.hd_modulus, &[f, fp, a, b, hf]);

    let spec = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);

        let range_ax = cle(d, p, a2, x);
        let range_xb = cle(d, p, x, b2);
        let range_ay = cle(d, p, a2, y);
        let range_yb = cle(d, p, y, b2);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);
        let hay_fv = d.fresh_fvar();
        let hay = d.kernel().fvar(hay_fv);
        let hyb_fv = d.fresh_fvar();
        let hyb = d.kernel().fvar(hyb_fv);

        // `|y - x| <= 1/(modulus e + 1)` -- the SAME closeness hypothesis the
        // original witness's own `spec` takes, since the modulus is the same.
        let neg_x = cneg(d, p, x);
        let diff_yx = cadd(d, p, y, neg_x);
        let abs_diff = cabs(d, p, diff_yx);
        let mod_e = d.apply(modulus, &[e]);
        let one_nat = d.num(1);
        let in_bound = ndsucc(d, p, one_nat, mod_e);
        let ofr_in = embed(d, p, in_bound);
        let hyp = cle(d, p, abs_diff, ofr_in);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let wide_ax = d.lemma(p.le_trans, &[a, a2, x, hlo, hax]);
        let wide_xb = d.lemma(p.le_trans, &[x, b2, b, hxb, hhi]);
        let wide_ay = d.lemma(p.le_trans, &[a, a2, y, hlo, hay]);
        let wide_yb = d.lemma(p.le_trans, &[y, b2, b, hyb, hhi]);
        let conclusion = d.lemma(
            p.hd_spec,
            &[
                f, fp, a, b, hf, e, x, y, wide_ax, wide_xb, wide_ay, wide_yb, h,
            ],
        );

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.hd_mk, &[f, fp, a2, b2, modulus, spec]);
    let value = {
        let with_hhi = d.lam_fv(hhi_fv, hhi_ty, mk_applied);
        let with_hmid = d.lam_fv(hmid_fv, hmid_ty, with_hhi);
        let with_hlo = d.lam_fv(hlo_fv, hlo_ty, with_hmid);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_hlo);
        let with_b2 = d.lam_fv(b2_fv, carrier, with_hf);
        let with_a2 = d.lam_fv(a2_fv, carrier, with_b2);
        let with_b = d.lam_fv(b_fv, carrier, with_a2);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let applied = hd_ty(d, p, f, fp, a2, b2);
        let with_hhi = d.arrow(hhi_ty, applied);
        let with_hmid = d.arrow(hmid_ty, with_hhi);
        let with_hlo = d.arrow(hlo_ty, with_hmid);
        let with_hf = d.arrow(hf_ty, with_hlo);
        let with_b2 = d.pi_fv(b2_fv, carrier, with_hf);
        let with_a2 = d.pi_fv(a2_fv, carrier, with_b2);
        let with_b = d.pi_fv(b_fv, carrier, with_a2);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_on_restrict,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// `CReal.sinFn` — general sine on `[0, 8/5]`, MECHANICALLY PARALLEL to
// `CReal.cosFnWide` above, per this task's own brief. Every step below is
// `cos_fn_wide`'s route with `Nat.add k k` (cosine's even exponent) replaced
// by `Nat.add (Nat.add k k) 1` (`sinTerm`'s own odd exponent,
// `creal/trig.rs::declare_sin_term`) wherever cosine used the doubled one.
// The one genuine extra cost, exactly where the task brief predicted it:
// `wide_bound_bridge`'s analogue ([`sin_wide_bound_bridge`]) needs ONE more
// step than `wide_bound_bridge` -- an extra `pow_add` split off the odd
// exponent's trailing `+1`, collapsing to a coefficient `2 · (half · R) =
// 2 · (4/5) = 8/5 = R` that has to be identified with the literal `R` by
// the SAME `Rat.normalize_mul_normalize` route `half_r_squared_eq_16_over_25`
// already uses for ITS OWN squaring step ([`two_y_eq_r_domain`], below).
// Nothing else in the route differs in shape from `cosFnWide`'s.
// ============================================================================

/// `Nat.add (Nat.add k k) 1` — `sinTerm`/`sinFnTerm`'s own odd index,
/// reproduced identically wherever this file needs it (structural hashing
/// makes every call site's result the same `ExprId`).
fn odd_index(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let dbl_k = d.add(k, k);
    let one_nat = d.num(1);
    d.add(dbl_k, one_nat)
}

/// `CReal.sinFnTerm : Nat → CReal → CReal := fun k x => mul (sinTerm k) (pow
/// x (Nat.add (Nat.add k k) 1))` — [`declare_cos_fn_term`]'s analogue at the
/// ODD exponent `sinTerm` itself already uses.
fn declare_sin_fn_term(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let sin_term_c = d.kernel().const_(p.sin_term, vec![]);
    let sin_term_k = d.apply(sin_term_c, &[k]);
    let odd_k = odd_index(d, k);
    let pow_x_odd = cpow(d, p, x, odd_k);
    let body = cmul(d, p, sin_term_k, pow_x_odd);

    let value = {
        let with_x = d.lam_fv(x_fv, carrier, body);
        d.lam_fv(k_fv, nat, with_x)
    };
    let ty = {
        let with_x = d.arrow(carrier, carrier);
        d.arrow(nat, with_x)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sin_fn_term,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(COS_FN_TERM_HEIGHT),
    })
}

/// `CReal.sinFnTerm_congr : ∀ k x y, Equiv x y → Equiv (sinFnTerm k x)
/// (sinFnTerm k y)` — [`declare_cos_fn_term_congr`]'s analogue, `mulPowCongr`
/// applied at the constant coefficient function `fun _ => sinTerm k` and the
/// ODD exponent `Nat.add (Nat.add k k) 1`.
fn declare_sin_fn_term_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
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

    let sin_term_c = d.kernel().const_(p.sin_term, vec![]);
    let sin_term_k = d.apply(sin_term_c, &[k]);
    let dummy_fv = d.fresh_fvar();
    let const_fn = d.lam_fv(dummy_fv, nat, sin_term_k);
    let odd_k = odd_index(d, k);

    let proof = d.lemma(p.mul_pow_congr, &[const_fn, odd_k, x, y, heq]);

    let value = {
        let with_heq = d.lam_fv(heq_fv, heq_ty, proof);
        let with_y = d.lam_fv(y_fv, carrier, with_heq);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(k_fv, nat, with_x)
    };
    let ty = {
        let sft_k_x = d.const_app(p.sin_fn_term, &[k, x]);
        let sft_k_y = d.const_app(p.sin_fn_term, &[k, y]);
        let concl = equiv(d, p, sft_k_x, sft_k_y);
        let with_heq = d.arrow(heq_ty, concl);
        let with_y = d.pi_fv(y_fv, carrier, with_heq);
        let with_x = d.pi_fv(x_fv, carrier, with_y);
        d.pi_fv(k_fv, nat, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sin_fn_term_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `le (abs (sinTerm k)) (expDominant (Nat.add (Nat.add k k) 1))` — the
/// TIGHT, pre-collapse bound `CReal.sinTermAbsLeDominant`'s own proof
/// computes internally (`creal/trig.rs::declare_sin_term_abs_le_dominant`),
/// one step before its final `exp_dominant_odd_le` collapse down to
/// `expDominant k`. [`cos_term_abs_le_dom_double`]'s analogue at the ODD
/// index rather than the doubled one.
///
/// Returns `(expDominant (Nat.add (Nat.add k k) 1), proof)`.
fn sin_term_abs_le_dom_odd(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> (ExprId, ExprId) {
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let sign_k = cpow(d, p, neg_one, k);
    let sign_abs = sign_abs_le_one(d, p, k);

    let odd_k = odd_index(d, k);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let e_term = d.apply(exp_term_c, &[odd_k]);
    let exp_dominant_c = d.kernel().const_(p.exp_dominant, vec![]);
    let dom_odd = d.apply(exp_dominant_c, &[odd_k]);

    let e_dom_bound = d.lemma(p.exp_term_abs_le_dominant, &[odd_k]);
    // e_dom_bound : le (abs e_term) dom_odd

    let prod_bound = d.lemma(
        p.abs_mul_le_of_bounds,
        &[sign_k, e_term, one_cc, dom_odd, sign_abs, e_dom_bound],
    );
    // prod_bound : le (abs (mul sign_k e_term)) (mul one_cc dom_odd)

    let mul_comm_1e = d.lemma(p.mul_comm, &[one_cc, dom_odd]);
    let mul_one_e = d.lemma(p.mul_one, &[dom_odd]);
    let mul_one_cc_dom = cmul(d, p, one_cc, dom_odd);
    let mul_dom_one = cmul(d, p, dom_odd, one_cc);
    let one_dom_equiv = echain(
        d,
        p,
        mul_one_cc_dom,
        &[(mul_dom_one, mul_comm_1e), (dom_odd, mul_one_e)],
    );

    let sin_term_k = cmul(d, p, sign_k, e_term);
    let abs_sin_term_k = cabs(d, p, sin_term_k);
    let refl_abs_sin = erefl(d, p, abs_sin_term_k);
    let abs_sin_le_dom_odd = d.lemma(
        p.le_congr,
        &[
            abs_sin_term_k,
            abs_sin_term_k,
            mul_one_cc_dom,
            dom_odd,
            refl_abs_sin,
            one_dom_equiv,
            prod_bound,
        ],
    );

    (dom_odd, abs_sin_le_dom_odd)
}

/// `CReal.sinFnTermAbsLeWide : ∀ x, le zero x → ∀ R, le x R → ∀ k, le (abs
/// (sinFnTerm k x)) (mul (expDominant (Nat.add (Nat.add k k) 1)) (pow R
/// (Nat.add (Nat.add k k) 1)))` — [`declare_cos_fn_term_abs_le_wide`]'s
/// analogue at the ODD exponent, via [`sin_term_abs_le_dom_odd`] in place of
/// [`cos_term_abs_le_dom_double`]. Otherwise byte-for-byte the same route:
/// `0 ≤ x ≤ R` (any `R`) via `le_trans`, base monotonicity
/// (`pow_le_pow_of_base_le`) plus nonnegativity (`pow_nonneg`) for the two
/// `abs`/`le` bookkeeping steps, folded by `abs_mul_le_of_bounds`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sin_fn_term_abs_le_wide(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
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
    let odd_k = odd_index(d, k);
    let pow_x_odd = cpow(d, p, x, odd_k);
    let pow_r_odd = cpow(d, p, r, odd_k);

    let (dom_odd_k, abs_sin_le_dom_odd) = sin_term_abs_le_dom_odd(d, p, k);

    // pow_x_odd <= pow_r_odd, zero <= pow_r_odd, zero <= pow_x_odd.
    let pow_bound = d.lemma(p.pow_le_pow_of_base_le, &[x, r, hax, hxr, odd_k]);
    let pow_r_nonneg = d.lemma(p.pow_nonneg, &[r, hr0, odd_k]);
    let pow_x_nonneg = d.lemma(p.pow_nonneg, &[x, hax, odd_k]);

    // neg pow_x_odd <= pow_r_odd, via neg pow_x_odd <= neg zero ~ zero <= pow_r_odd.
    let neg_pow = cneg(d, p, pow_x_odd);
    let neg_zero = cneg(d, p, zero_c);
    let step1 = d.lemma(p.neg_le_neg, &[zero_c, pow_x_odd, pow_x_nonneg]); // le neg_pow neg_zero
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
        &[neg_pow, zero_c, pow_r_odd, neg_pow_le_zero, pow_r_nonneg],
    );

    let abs_pow_le_r = d.lemma(p.abs_le, &[pow_x_odd, pow_r_odd, pow_bound, neg_pow_le_r]);

    // abs (mul (sinTerm k) pow_x_odd) <= mul dom_odd_k pow_r_odd.
    let sin_term_c = d.kernel().const_(p.sin_term, vec![]);
    let sin_term_k = d.apply(sin_term_c, &[k]);
    let mul_bound = d.lemma(
        p.abs_mul_le_of_bounds,
        &[
            sin_term_k,
            pow_x_odd,
            dom_odd_k,
            pow_r_odd,
            abs_sin_le_dom_odd,
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
        let sft_k_x = d.const_app(p.sin_fn_term, &[k, x]);
        let abs_sft = cabs(d, p, sft_k_x);
        let bound = cmul(d, p, dom_odd_k, pow_r_odd);
        let concl = cle(d, p, abs_sft, bound);
        let with_k = d.pi_fv(k_fv, nat, concl);
        let with_hxr = d.arrow(hxr_ty, with_k);
        let with_r = d.pi_fv(r_fv, carrier, with_hxr);
        let with_hax = d.arrow(hax_ty, with_r);
        d.pi_fv(x_fv, carrier, with_hax)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sin_fn_term_abs_le_wide,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.sinFnTerm`, `CReal.sinFnTerm_congr` and
/// `CReal.sinFnTermAbsLeWide` — rung 1 of general sine (the task brief's own
/// scoping): the series term at a point, its `Equiv`-congruence, and the
/// odd-exponent domination bound past `[0, 1]`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sin_fn_term_family(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_sin_fn_term(d, p)?;
    declare_sin_fn_term_congr(d, p)?;
    declare_sin_fn_term_abs_le_wide(d, p)
}

/// `Equiv (pow y (Nat.num 1)) y` — `pow y (succ zero)` ι-reduces to `mul
/// (pow y zero) y = mul one y` (`CReal.pow`'s own `Nat.rec` definition,
/// `creal/power.rs::declare_pow`), so this is `mul_comm` + `mul_one`
/// chained, ascribed against the ι-reduced LHS via the kernel's own defeq
/// check — this file's "computed, not extracted" convention (see
/// [`cos_fn_term_uc`]'s own doc comment for the same technique), no
/// `pow_succ`/`pow_zero` lemma application needed.
fn pow_one_equiv_here(d: &mut IntDev<'_>, p: CRealPrelude, y: ExprId) -> ExprId {
    let one_cc = one_c(d, p);
    let one_nat = d.num(1);
    let pow_y_one = cpow(d, p, y, one_nat);
    let mul_y_one = cmul(d, p, y, one_cc);
    let step_a = d.lemma(p.mul_comm, &[one_cc, y]);
    let step_b = d.lemma(p.mul_one, &[y]);
    echain(d, p, pow_y_one, &[(mul_y_one, step_a), (y, step_b)])
}

/// `(Equiv y (embed q1), q1, n2, e2, h2)`, `y := mul half R`, `q1` computing
/// to `Rat.normalize (Int.ofNat 4) 5 _` (`n2 := Int.ofNat 4`, `e2 := 5`,
/// `h2` its positivity proof) — the FIRST half of
/// [`half_r_squared_eq_16_over_25`]'s own computation (`half_rat * R_rat =
/// 8/10 = 4/5`), reproduced here (rather than refactoring that function's
/// return type, which [`declare_cos_fn_wide`] already depends on unchanged)
/// so [`two_y_eq_r_domain`] can build on it independently, returning the raw
/// `(n2, e2, h2)` triple too so that caller can feed it straight into a
/// SECOND `normalize_mul_normalize` application without re-deriving `q1`'s
/// own components.
fn half_r_eq_q1(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(ExprId, ExprId, ExprId, ExprId, ExprId), KernelError> {
    let rat = p.rat;
    let half_rat = super::exponential::half_rat(d, p);
    let r_rat = r_domain_rat(d, p);

    // step0 : Eq Rat (Rat.mul half_rat R_rat) (normalize (1*8) (2*5) _).
    let one_a = d.num(1);
    let one_int = d.of_nat(one_a);
    let one_b = d.num(1);
    let succ1 = d.succ(one_b);
    let one_c_nat = d.num(1);
    let h_a = one_le_succ(d, one_c_nat);
    let eight_a = d.num(8);
    let eight_int = d.of_nat(eight_a);
    let four_a = d.num(4);
    let succ4 = d.succ(four_a);
    let four_b = d.num(4);
    let h_b = one_le_succ(d, four_b);
    let step0 = d.lemma(
        rat.normalize_mul_normalize,
        &[one_int, succ1, h_a, eight_int, succ4, h_b],
    );
    let (_, q0_raw) = req_sides(d, step0)?;

    // step1 : Eq Rat (normalize 8 10 _) (normalize 4 5 _), via
    // normalize_congr at the cross-multiplication identity 8*5 = 4*10.
    let n8 = d.num(8);
    let n1 = d.of_nat(n8);
    let n9 = d.num(9);
    let e1 = d.succ(n9); // 10
    let h1 = one_le_succ(d, n9);
    let n4 = d.num(4);
    let n2 = d.of_nat(n4);
    let n4b = d.num(4);
    let e2 = d.succ(n4b); // 5
    let n4c = d.num(4);
    let h2 = one_le_succ(d, n4c);
    let hyp = {
        let e2_z = d.of_nat(e2);
        let lhs = d.imul(n1, e2_z);
        d.irefl(lhs)
    };
    let step1 = d.lemma(rat.normalize_congr, &[n1, e1, h1, n2, e2, h2, hyp]);
    let (_, q1) = req_sides(d, step1)?;

    let half_r_eq = {
        let target_lhs = rmul_here(d, half_rat, r_rat);
        let motive_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            crate::rat_prelude::ops::req(d, target_lhs, x)
        };
        rat_rewrite(d, q0_raw, q1, step1, step0, &motive_at)
    };

    let half_c = super::exponential::half(d, p);
    let r_c = r_domain(d, p);
    let y = cmul(d, p, half_c, r_c);
    let y_eq = {
        let step_of_rat = d.lemma(p.of_rat_mul, &[half_rat, r_rat]); // Equiv y (embed(Rat.mul half_rat r_rat))
        let half_r_raw = rmul_here(d, half_rat, r_rat);
        let embed_raw = embed(d, p, half_r_raw);
        let embed_q1 = embed(d, p, q1);
        let bridge = embed_eq_to_equiv_here(d, p, half_r_raw, q1, half_r_eq);
        d.lemma(
            p.equiv_trans,
            &[y, embed_raw, embed_q1, step_of_rat, bridge],
        )
    };

    Ok((y_eq, q1, n2, e2, h2))
}

/// `mul half R` — reproduced as a tiny helper so [`two_y_eq_r_domain`] does
/// not have to thread `y` through as an extra parameter; cheap to
/// reconstruct (two `pub(super)` lookups plus one `cmul`), and structural
/// hashing makes every call site's result the identical `ExprId`.
fn y_from(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let half_c = super::exponential::half(d, p);
    let r_c = r_domain(d, p);
    cmul(d, p, half_c, r_c)
}

/// `Equiv (mul two y) R`, `y := mul half R`, `R := ofRat (natDivSucc 8 4)` —
/// `2 · (4/5) = 8/5 = R`, verified by `Rat.normalize_mul_normalize` (fusing
/// `two_rat * q1` into `normalize (2*4) (1*5) _`, which COMPUTES —
/// ordinary `Int.mul`/`Nat.mul` on concrete literals, no `Rat.normalize`
/// GCD-reduction involved on EITHER side, unlike
/// [`half_r_squared_eq_16_over_25`]'s own `8/10 -> 4/5` step, which
/// genuinely needs `normalize_congr`'s cross-multiplication because `8/10`
/// and `4/5` are a DIFFERENT numerator/denominator pair — down to the SAME
/// `(8, 5)` pair `R`'s own `natDivSucc 8 4` unfolds to. This is exactly the
/// "one extra factor" the odd exponent costs
/// [`sin_wide_bound_bridge`] over [`wide_bound_bridge`], and no more.
fn two_y_eq_r_domain(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<ExprId, KernelError> {
    let rat = p.rat;
    let (y_eq, q1, q1_n, q1_e, q1_h) = half_r_eq_q1(d, p)?;

    let (two_rat, two_z, h1_two) = two_normalize(d, p);
    let one_nat_denom = d.num(1);

    // step0 : Eq Rat (Rat.mul two_rat q1) (normalize (Int.mul two_z q1_n)
    // (Nat.mul one_nat_denom q1_e) _), whose RHS computes (2*4=8, 1*5=5) to
    // the SAME (8, 5) pair `r_domain_rat`'s own `natDivSucc 8 4` unfolds to.
    let step0 = d.lemma(
        rat.normalize_mul_normalize,
        &[two_z, one_nat_denom, h1_two, q1_n, q1_e, q1_h],
    );

    let r_c = r_domain(d, p);
    let embed_q1 = embed(d, p, q1);
    let two_c = two(d, p);
    let refl_two = d.lemma(p.equiv_refl, &[two_c]);
    let y = y_from(d, p);

    let mul_two_y = cmul(d, p, two_c, y);
    let step_congr = d.lemma(p.mul_congr, &[two_c, two_c, y, embed_q1, refl_two, y_eq]);
    let mul_two_embedq1 = cmul(d, p, two_c, embed_q1);

    let step_ofrat = d.lemma(p.of_rat_mul, &[two_rat, q1]);
    // step_ofrat : Equiv (mul two_c embed_q1) (embed (Rat.mul two_rat q1))
    let two_q1_raw = rmul_here(d, two_rat, q1);
    let embed_prod = embed(d, p, two_q1_raw);

    let r_rat = r_domain_rat(d, p);
    // step0's actual RHS is DEFEQ to r_rat (matching (num, denom) literals,
    // no GCD reduction needed) -- ascribed here via `embed_eq_to_equiv_here`,
    // relying on that defeq exactly the way this file's other bridges do.
    let bridge = embed_eq_to_equiv_here(d, p, two_q1_raw, r_rat, step0);

    Ok(echain(
        d,
        p,
        mul_two_y,
        &[
            (mul_two_embedq1, step_congr),
            (embed_prod, step_ofrat),
            (r_c, bridge),
        ],
    ))
}

/// `CReal.sinDominant16Over25 : Nat → CReal := fun k => mul R (pow (ofRat
/// (natDivSucc 16 24)) k)`, `R := ofRat (natDivSucc 8 4)` —
/// [`declare_cos_dominant_16_over_25`]'s analogue at coefficient `R` rather
/// than `two`: the odd exponent's extra factor of the base collapses
/// ([`sin_wide_bound_bridge`]) to `2 · (half · R) = 2 · (4/5) = 8/5 = R`
/// (verified by [`two_y_eq_r_domain`], not assumed from the numeric
/// coincidence).
fn declare_sin_dominant_16_over_25(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let (x, ..) = ratio_16_over_25_witnesses(d, p);
    let r_c = r_domain(d, p);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let pow_x_k = cpow(d, p, x, k);
    let body = cmul(d, p, r_c, pow_x_k);

    let value = d.lam_fv(k_fv, nat, body);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sin_dominant_16_over_25,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(COS_FN_TERM_HEIGHT + 2),
    })
}

/// A CONCRETE `(K, proof : sum_range_cauchy_body (sumRange
/// sinDominant16Over25) K)` —
/// [`cos_dominant_16_over_25_cauchy_body_concrete`]'s analogue at
/// coefficient `c := R` (`q := R`'s own `Rat` witness, `r_domain_rat`)
/// rather than `c := two`. [`mul_ordered_half_body`] is generic in `c`/`q`,
/// so this is the SAME construction, confirmed to finish unchanged once the
/// coefficient is substituted, exactly as predicted by
/// [`cos_dominant_16_over_25_cauchy_body_concrete`]'s own doc comment.
fn sin_dominant_16_over_25_cauchy_body_concrete(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let (x, _, _, _, n24, _, _) = ratio_16_over_25_witnesses(d, p);
    let raw_pow_x = pow_fn_local(d, p, x);
    let s_fn = d.const_app(p.sum_range, &[raw_pow_x]);
    let r_c = r_domain(d, p);
    let r_rat = r_domain_rat(d, p);

    let k_s = geom_16_over_25_k_final(d, n24);
    let two_nat = d.num(2);
    let ka = magnitude_of(d, p, r_c);
    let kg_num = NatOps::mul(d, ka, k_s);
    let ka2 = NatOps::mul(d, ka, two_nat);
    let k_g = d.add(kg_num, ka2);

    // `G := fun n => mul R (S n)`, `S := sumRange (pow (16/25) ·)`.
    let g_fn = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.apply(s_fn, &[n]);
        let prod = cmul(d, p, r_c, sn);
        d.lam_fv(n_fv, nat, prod)
    };

    let ordered_half = |d: &mut IntDev<'_>, a: ExprId, b: ExprId, hab: ExprId| -> ExprId {
        let (_, proof) = mul_ordered_half_body(
            d,
            p,
            r_c,
            r_rat,
            s_fn,
            k_s,
            a,
            b,
            &|d, aa, bb, hh| d.lemma(p.geom_cauchy_ordered_16_over_25, &[aa, bb, hh]),
            hab,
        );
        proof
    };

    let g_case_proof = promote_ordered_half_to_full(d, p, g_fn, k_g, &ordered_half);

    let sin_dominant_const = d.kernel().const_(p.sin_dominant_16_over_25, vec![]);
    let f_fn = d.const_app(p.sum_range, &[sin_dominant_const]);
    let heq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.lemma(p.mul_sum_range, &[r_c, raw_pow_x, n]);
        d.lam_fv(n_fv, nat, body)
    };

    cauchy_body_transport(d, p, g_fn, f_fn, heq, k_g, g_case_proof)
}

/// `CReal.sinDominant16Over25CauchyBody : sum_range_cauchy_body (sumRange
/// sinDominant16Over25) K` for the concrete `K`
/// [`sin_dominant_16_over_25_cauchy_body_concrete`] returns — the raw,
/// non-existential Cauchy witness `weierstrassMTest`'s `hcauchy` parameter
/// needs, at coefficient `R`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sin_dominant_16_over_25_cauchy_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let (k_final, proof) = sin_dominant_16_over_25_cauchy_body_concrete(d, p);
    let sin_dominant_const = d.kernel().const_(p.sin_dominant_16_over_25, vec![]);
    let f_fn = d.const_app(p.sum_range, &[sin_dominant_const]);
    let ty = sum_range_cauchy_body(d, p, f_fn, k_final);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sin_dominant_16_over_25_cauchy_body,
        uparams: vec![],
        ty,
        value: proof,
    })
}

/// Admit `CReal.sinDominant16Over25` and its raw Cauchy body — rung 2's
/// dominating-series half.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sin_fn_dominant(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_sin_dominant_16_over_25(d, p)?;
    declare_sin_dominant_16_over_25_cauchy_body(d, p)
}

/// `Equiv (mul (expDominant (Nat.add (Nat.add j j) 1)) (pow R (Nat.add
/// (Nat.add j j) 1))) (sinDominant16Over25 j)`, `R := ofRat (natDivSucc 8
/// 4)` — [`wide_bound_bridge`]'s analogue at the ODD exponent
/// `sinFnTerm`/`sinTerm` themselves already use. ONE more step than
/// [`wide_bound_bridge`]: the odd exponent `2j+1` needs an extra `pow_add`
/// split off its trailing `+1` (`pow y (2j+1)` reduces DEFINITIONALLY —
/// `Nat.add` recurses on its right argument — to `mul (pow y (2j)) y`, so
/// no lemma is needed for that reduction itself, only for the resulting
/// extra factor of `y`, collapsed by [`pow_one_equiv_here`]) plus
/// identifying the resulting coefficient `2 · y = 2 · (4/5) = 8/5` with the
/// literal `R` via [`two_y_eq_r_domain`] — exactly the "one extra factor"
/// the task brief predicted, and no more.
fn sin_wide_bound_bridge(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    j: ExprId,
) -> Result<ExprId, KernelError> {
    let half_c = super::exponential::half(d, p);
    let r_c = r_domain(d, p);
    let two_c = two(d, p);
    let dbl_j = d.add(j, j);
    let one_nat = d.num(1);
    let odd_j = d.add(dbl_j, one_nat);

    let pow_half_odd = cpow(d, p, half_c, odd_j);
    let pow_r_odd = cpow(d, p, r_c, odd_j);
    let start = {
        let ed_odd = cmul(d, p, two_c, pow_half_odd);
        cmul(d, p, ed_odd, pow_r_odd)
    };

    // s1 := two * (pow_half_odd * pow_r_odd), via mul_assoc.
    let inner_hr = cmul(d, p, pow_half_odd, pow_r_odd);
    let s1 = cmul(d, p, two_c, inner_hr);
    let h1 = d.lemma(p.mul_assoc, &[two_c, pow_half_odd, pow_r_odd]);

    let y = cmul(d, p, half_c, r_c);
    let refl_two = d.lemma(p.equiv_refl, &[two_c]);

    // s2 := two * (pow y odd_j), via pow_mul_distrib(half, R, odd_j).
    let distrib1 = d.lemma(p.pow_mul_distrib, &[half_c, r_c, odd_j]);
    let pow_y_odd = cpow(d, p, y, odd_j);
    let h2 = d.lemma(
        p.mul_congr,
        &[two_c, two_c, inner_hr, pow_y_odd, refl_two, distrib1],
    );
    let s2 = cmul(d, p, two_c, pow_y_odd);

    // s3 := two * (mul pow_y_dbl pow_y_one), via pow_add(y, dbl_j, 1).
    let pow_y_dbl = cpow(d, p, y, dbl_j);
    let pow_y_one = cpow(d, p, y, one_nat);
    let split1 = d.lemma(p.pow_add, &[y, dbl_j, one_nat]);
    let mul_dbl_one = cmul(d, p, pow_y_dbl, pow_y_one);
    let h3 = d.lemma(
        p.mul_congr,
        &[two_c, two_c, pow_y_odd, mul_dbl_one, refl_two, split1],
    );
    let s3 = cmul(d, p, two_c, mul_dbl_one);

    // s4 := two * (mul pow_y_dbl y), collapsing `pow y 1` to `y`.
    let pow_one_eq = pow_one_equiv_here(d, p, y);
    let refl_dbl = d.lemma(p.equiv_refl, &[pow_y_dbl]);
    let inner_c1 = d.lemma(
        p.mul_congr,
        &[pow_y_dbl, pow_y_dbl, pow_y_one, y, refl_dbl, pow_one_eq],
    );
    let mul_dbl_y = cmul(d, p, pow_y_dbl, y);
    let h4 = d.lemma(
        p.mul_congr,
        &[two_c, two_c, mul_dbl_one, mul_dbl_y, refl_two, inner_c1],
    );
    let s4 = cmul(d, p, two_c, mul_dbl_y);

    // s5 := two * (mul (mul pow_y_j pow_y_j) y), via pow_add(y, j, j)
    // splitting `pow_y_dbl` inside the left factor.
    let pow_y_j = cpow(d, p, y, j);
    let mul_jj = cmul(d, p, pow_y_j, pow_y_j);
    let split2 = d.lemma(p.pow_add, &[y, j, j]);
    let refl_y = d.lemma(p.equiv_refl, &[y]);
    let inner_c2 = d.lemma(p.mul_congr, &[pow_y_dbl, mul_jj, y, y, split2, refl_y]);
    let mul_jj_y = cmul(d, p, mul_jj, y);
    let h5 = d.lemma(
        p.mul_congr,
        &[two_c, two_c, mul_dbl_y, mul_jj_y, refl_two, inner_c2],
    );
    let s5 = cmul(d, p, two_c, mul_jj_y);

    // s6 := two * (mul (pow yy j) y), via pow_mul_distrib(y, y, j) fusing
    // `mul_jj` inside the left factor.
    let yy = cmul(d, p, y, y);
    let pow_yy_j = cpow(d, p, yy, j);
    let distrib2 = d.lemma(p.pow_mul_distrib, &[y, y, j]);
    let inner_c3 = d.lemma(p.mul_congr, &[mul_jj, pow_yy_j, y, y, distrib2, refl_y]);
    let pow_yy_j_y = cmul(d, p, pow_yy_j, y);
    let h6 = d.lemma(
        p.mul_congr,
        &[two_c, two_c, mul_jj_y, pow_yy_j_y, refl_two, inner_c3],
    );
    let s6 = cmul(d, p, two_c, pow_yy_j_y);

    // s7 := two * (mul y (pow yy j)), via mul_comm.
    let comm_step = d.lemma(p.mul_comm, &[pow_yy_j, y]);
    let y_pow_yy_j = cmul(d, p, y, pow_yy_j);
    let h7 = d.lemma(
        p.mul_congr,
        &[two_c, two_c, pow_yy_j_y, y_pow_yy_j, refl_two, comm_step],
    );
    let s7 = cmul(d, p, two_c, y_pow_yy_j);

    // s8 := (two * y) * (pow yy j), via mul_assoc (reversed).
    let two_y = cmul(d, p, two_c, y);
    let s8 = cmul(d, p, two_y, pow_yy_j);
    let assoc_fwd = d.lemma(p.mul_assoc, &[two_c, y, pow_yy_j]);
    // assoc_fwd : Equiv (mul (mul two y) (pow yy j)) (mul two (mul y (pow yy j))) = Equiv s8 s7
    let h8 = d.lemma(p.equiv_symm, &[s8, s7, assoc_fwd]);

    // s9 := R * (pow yy j), via two_y_eq_r_domain.
    let two_y_eq_r = two_y_eq_r_domain(d, p)?;
    let refl_pow_yy_j = d.lemma(p.equiv_refl, &[pow_yy_j]);
    let h9 = d.lemma(
        p.mul_congr,
        &[two_y, r_c, pow_yy_j, pow_yy_j, two_y_eq_r, refl_pow_yy_j],
    );
    let s9 = cmul(d, p, r_c, pow_yy_j);

    // target := R * (pow embed_q2 j), rewriting the base via
    // half_r_squared_eq_16_over_25.
    let yy_eq = half_r_squared_eq_16_over_25(d, p)?;
    let yy_ty = d.kernel().infer(yy_eq)?;
    let (_, embed_q2) = two_sides(d, yy_ty);
    let pow_target_j = cpow(d, p, embed_q2, j);
    let h10 = d.lemma(p.pow_congr, &[yy, embed_q2, yy_eq, j]);
    let refl_r = d.lemma(p.equiv_refl, &[r_c]);
    let h10c = d.lemma(
        p.mul_congr,
        &[r_c, r_c, pow_yy_j, pow_target_j, refl_r, h10],
    );
    let target = cmul(d, p, r_c, pow_target_j);

    Ok(echain(
        d,
        p,
        start,
        &[
            (s1, h1),
            (s2, h2),
            (s3, h3),
            (s4, h4),
            (s5, h5),
            (s6, h6),
            (s7, h7),
            (s8, h8),
            (s9, h9),
            (target, h10c),
        ],
    ))
}

/// `fun n pt => sumRange (fun j => sinFnTerm j pt) n` — [`cos_fn_partial_sums_fn`]'s
/// analogue for `sinFn`.
fn sin_fn_partial_sums_fn(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    nat: ExprId,
) -> ExprId {
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let f_pt = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let body = d.const_app(p.sin_fn_term, &[j, pt]);
        d.lam_fv(j_fv, nat, body)
    };
    let body = d.const_app(p.sum_range, &[f_pt, n]);
    let with_pt = d.lam_fv(pt_fv, carrier, body);
    d.lam_fv(n_fv, nat, with_pt)
}

/// Admit `CReal.sinFn` and `CReal.sinFnUniformConverges` — rung 2:
/// [`declare_cos_fn_wide`]'s analogue, `weierstrassMTest` applied at `f :=
/// sinFnTerm`, `mseq := sinDominant16Over25`, `a := zero`, `b := R`,
/// bridging [`declare_sin_fn_term_abs_le_wide`]'s domination bound to
/// [`declare_sin_dominant_16_over_25`]'s dominating series via
/// [`sin_wide_bound_bridge`]. Run after [`declare_sin_fn_term_family`] and
/// [`declare_sin_fn_dominant`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sin_fn(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let r_c = r_domain(d, p);

    let f0 = d.kernel().const_(p.sin_fn_term, vec![]);
    let mseq0 = d.kernel().const_(p.sin_dominant_16_over_25, vec![]);

    let hab0 = hab_zero_r(d, p);

    // hcong0 : forall j p q, Equiv p q -> Equiv (f0 j p) (f0 j q).
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
        let body = d.lemma(p.sin_fn_term_congr, &[j, pp, qq, heq]);
        let with_heq = d.lam_fv(heq_fv, heq_ty, body);
        let with_qq = d.lam_fv(qq_fv, carrier, with_heq);
        let with_pp = d.lam_fv(pp_fv, carrier, with_qq);
        d.lam_fv(j_fv, nat, with_pp)
    };

    let (k_g, hcauchy0) = sin_dominant_16_over_25_cauchy_body_concrete(d, p);

    // hdom0 : forall j pt, le zero pt -> le pt R -> le (abs (f0 j pt)) (mseq0 j).
    let hdom0 = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxr_fv = d.fresh_fvar();
        let hxr = d.kernel().fvar(hxr_fv);

        let raw_bound = d.lemma(p.sin_fn_term_abs_le_wide, &[pt, hax, r_c, hxr, j]);

        let bridge = sin_wide_bound_bridge(d, p, j)?;

        let abs_sft = {
            let sft = d.const_app(p.sin_fn_term, &[j, pt]);
            cabs(d, p, sft)
        };
        let refl_lhs = d.lemma(p.equiv_refl, &[abs_sft]);
        let bound = {
            let ed = d.kernel().const_(p.exp_dominant, vec![]);
            let odd_j = odd_index(d, j);
            let ed_odd = d.apply(ed, &[odd_j]);
            let pow_r_odd = cpow(d, p, r_c, odd_j);
            cmul(d, p, ed_odd, pow_r_odd)
        };
        let mseq0_j = d.apply(mseq0, &[j]);
        let transported = d.lemma(
            p.le_congr,
            &[
                abs_sft, abs_sft, bound, mseq0_j, refl_lhs, bridge, raw_bound,
            ],
        );

        let hxr_ty = cle(d, p, pt, r_c);
        let hax_ty = cle(d, p, zero_c, pt);
        let with_hxr = d.lam_fv(hxr_fv, hxr_ty, transported);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxr);
        let with_pt = d.lam_fv(pt_fv, carrier, with_hax);
        d.lam_fv(j_fv, nat, with_pt)
    };

    let u0 = d.lemma(
        p.weierstrass_m_test,
        &[f0, mseq0, zero_c, r_c, hab0, hcong0, k_g, hdom0, hcauchy0],
    );
    let ty0 = d.kernel().infer(u0)?;

    let (inner1, _b0) = unapp(d, ty0);
    let (inner2, _a0) = unapp(d, inner1);
    let (_inner3, g0) = unapp(d, inner2);

    let sin_fn_ty = d.arrow(carrier, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sin_fn,
        uparams: vec![],
        ty: sin_fn_ty,
        value: g0,
        hint: ReducibilityHint::Regular(COS_FN_TERM_HEIGHT + 3),
    })?;

    let big_f = sin_fn_partial_sums_fn(d, p, carrier, nat);
    let sin_fn_c = d.kernel().const_(p.sin_fn, vec![]);
    let ty = d.const_app(p.uniform_converges_on, &[big_f, sin_fn_c, zero_c, r_c]);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sin_fn_uniform_converges,
        uparams: vec![],
        ty,
        value: u0,
    })
}

// ============================================================================
// `CReal.sinFnUniformlyContinuous`
// ============================================================================
//
// Route: [`declare_cos_fn_wide_uniformly_continuous`]'s, verbatim in shape.
// The one difference: [`pow_uc`] (the nested induction over `pow`'s base at
// a symbolic exponent) is already generic in ITS OWN exponent argument, so
// [`sin_fn_term_uc`] applies it directly at `m := Nat.add (Nat.add k k) 1`
// -- no SEPARATE induction is needed for the odd exponent.

/// `UniformlyContinuousOn (fun pt => sinFnTerm k pt) zero R`, for symbolic
/// `k`. [`cos_fn_term_uc`]'s analogue.
fn sin_fn_term_uc(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    nat: ExprId,
    zero_c: ExprId,
    r_c: ExprId,
    hab0: ExprId,
    pow_uc: ExprId,
    k: ExprId,
) -> ExprId {
    let k_id = fvar_id(d, k);
    let free_k = [(k_id, nat)];

    let odd_k = odd_index(d, k);
    let pow_odd_fn = pow_base_fn(d, p, carrier, odd_k);
    let huc_pow_odd = d.apply(pow_uc, &[odd_k]);

    let sin_term_c = d.kernel().const_(p.sin_term, vec![]);
    let sin_term_k = d.apply(sin_term_c, &[k]);
    let const_fn = {
        let pt_fv = d.fresh_fvar();
        d.lam_fv(pt_fv, carrier, sin_term_k)
    };
    let huc_const = d.lemma(p.uniformly_continuous_const, &[sin_term_k, zero_c, r_c]);

    let (k1, hb1) = bounded_via_uc(d, p, const_fn, zero_c, r_c, huc_const, hab0, &free_k);
    let (k2, hb2) = bounded_via_uc(d, p, pow_odd_fn, zero_c, r_c, huc_pow_odd, hab0, &free_k);

    d.lemma(
        p.uniformly_continuous_mul,
        &[
            const_fn,
            pow_odd_fn,
            zero_c,
            r_c,
            huc_const,
            huc_pow_odd,
            k1,
            k2,
            hb1,
            hb2,
        ],
    )
}

/// Admit `CReal.sinFnUniformlyContinuous : UniformlyContinuousOn sinFn zero
/// (ofRat (natDivSucc 8 4))` — [`declare_cos_fn_wide_uniformly_continuous`]'s
/// analogue.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sin_fn_uniformly_continuous(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let r_c = r_domain(d, p);
    let hab0 = hab_zero_r(d, p);

    // `pow_uc : ∀ m, UniformlyContinuousOn (fun pt => pow pt m) zero R` --
    // the nested induction over `pow`'s base, shared with
    // [`declare_sin_fn_uniformly_continuous`] and the derivative section's
    // two Skolem bound builders rather than reproduced per call site.
    let pow_uc = pow_uc_fn(d, p, carrier, nat, zero_c, r_c, hab0);

    // --- outer induction: partial-sum uniform continuity, over `n` -------
    let big_f = sin_fn_partial_sums_fn(d, p, carrier, nat);

    let sum_motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let fv = d.apply(big_f, &[v]);
        d.const_app(p.uniformly_continuous_on, &[fv, zero_c, r_c])
    };
    let sum_base = |d: &mut IntDev<'_>| -> ExprId {
        d.lemma(p.uniformly_continuous_const, &[zero_c, zero_c, r_c])
    };
    let sum_step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let sum_j_fn = {
            let pt_fv = d.fresh_fvar();
            let pt = d.kernel().fvar(pt_fv);
            let f_pt = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let body = d.const_app(p.sin_fn_term, &[k, pt]);
                d.lam_fv(k_fv, nat, body)
            };
            let body = d.const_app(p.sum_range, &[f_pt, j]);
            d.lam_fv(pt_fv, carrier, body)
        };
        let term_j_fn = {
            let pt_fv = d.fresh_fvar();
            let pt = d.kernel().fvar(pt_fv);
            let body = d.const_app(p.sin_fn_term, &[j, pt]);
            d.lam_fv(pt_fv, carrier, body)
        };
        let term_j_uc = sin_fn_term_uc(d, p, carrier, nat, zero_c, r_c, hab0, pow_uc, j);
        d.lemma(
            p.uniformly_continuous_add,
            &[sum_j_fn, term_j_fn, zero_c, r_c, ih, term_j_uc],
        )
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hc_at_n = induct_ty(d, &sum_motive, &sum_base, &sum_step, n);
    let hc = d.lam_fv(n_fv, nat, hc_at_n);
    // hc : ∀ n, UniformlyContinuousOn (App(big_f, n)) zero R.

    let g0 = d.kernel().const_(p.sin_fn, vec![]);
    let hu = d.kernel().const_(p.sin_fn_uniform_converges, vec![]);

    let value = d.lemma(
        p.uniform_limit_uniformly_continuous,
        &[big_f, g0, zero_c, r_c, hu, hc],
    );
    let ty = d.const_app(p.uniformly_continuous_on, &[g0, zero_c, r_c]);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sin_fn_uniformly_continuous,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// The derivative of `cosFnWide`'s partial sums (lane 159 step 1)
// ============================================================================
//
// `CReal.hasDerivative_pow` demands TWO Skolem `BoundedOn` functions -- `kb`
// bounding `fun r => pow r n` and `kd` bounding `fun x => mul (ofNat (succ
// n)) (pow x n)`, each at EVERY `n`. Neither is hand-derived here: this file
// already builds `pow` uniform continuity at a symbolic exponent
// ([`pow_uc_fn`], extracted below from the two verbatim copies
// `declare_cos_fn_wide_uniformly_continuous` and
// `declare_sin_fn_uniformly_continuous` each carried), and
// `CReal.bounded_of_uniformly_continuous` turns that into a `BoundedOn` with
// a COMPUTED index. Lambda-abstracting that index over the exponent IS the
// Skolem function -- so the two hypotheses that looked like the obstacle
// cost one `d.lam_fv` each.
//
// The crux is the index-shifted coefficient identity. `cosFnTerm k x :=
// cosTerm k * x^(k+k)` and `sinFnTerm k x := sinTerm k * x^(2k+1)`, so
// `d/dx cosFnTerm (j+1) = cosTerm (j+1) * (2j+2) * x^(2j+1)` and matching it
// against `-sinFnTerm j` needs `cosTerm (j+1) * (2j+2) ~ -sinTerm j`. With
// `cosTerm k := (-1)^k * expTerm (k+k)` and `sinTerm k := (-1)^k * expTerm
// (2k+1)` that reduces, after one `(-1)^(j+1) = -(-1)^j` step, to
// `(m+1) * expTerm (m+1) ~ expTerm m` at `m := 2j+1` -- i.e. `(m+1)/(m+1)! =
// 1/m!`, which is [`declare_exp_term_succ_scale`] and is NOT expensive:
// `Rat.normalize_mul_normalize` fuses the product into one `normalize` and
// `Rat.normalize_congr` closes the cross-multiplication against
// `Nat.factorial_succ`. No `Rat.inv`, no case split.

/// `∀ m, UniformlyContinuousOn (fun pt => pow pt m) zero R` -- the nested
/// induction over `pow`'s BASE at a symbolic exponent.
///
/// Extracted from [`declare_cos_fn_wide_uniformly_continuous`] and
/// [`declare_sin_fn_uniformly_continuous`], which carried byte-identical
/// copies of it, and now needed a third and fourth time by
/// [`pow_bounded_skolem`]/[`pow_deriv_bounded_skolem`].
fn pow_uc_fn(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    nat: ExprId,
    zero_c: ExprId,
    r_c: ExprId,
    hab0: ExprId,
) -> ExprId {
    let id_fn = {
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        d.lam_fv(pt_fv, carrier, pt)
    };
    let huc_id = d.lemma(p.uniformly_continuous_id, &[zero_c, r_c]);

    let pow_motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let f = pow_base_fn(d, p, carrier, v);
        d.const_app(p.uniformly_continuous_on, &[f, zero_c, r_c])
    };
    let pow_base = |d: &mut IntDev<'_>| -> ExprId {
        let one_cc = one_c(d, p);
        d.lemma(p.uniformly_continuous_const, &[one_cc, zero_c, r_c])
    };
    let pow_step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let pow_j_fn = pow_base_fn(d, p, carrier, j);
        let j_id = fvar_id(d, j);
        let ih_id = fvar_id(d, ih);
        let ih_ty = pow_motive(d, j);
        let (k1, hb1) = bounded_via_uc(
            d,
            p,
            pow_j_fn,
            zero_c,
            r_c,
            ih,
            hab0,
            &[(j_id, nat), (ih_id, ih_ty)],
        );
        let (k2, hb2) = bounded_via_uc(d, p, id_fn, zero_c, r_c, huc_id, hab0, &[]);
        d.lemma(
            p.uniformly_continuous_mul,
            &[pow_j_fn, id_fn, zero_c, r_c, ih, huc_id, k1, k2, hb1, hb2],
        )
    };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let pow_uc_at_m = induct_ty(d, &pow_motive, &pow_base, &pow_step, m);
    d.lam_fv(m_fv, nat, pow_uc_at_m)
}

/// `(kb, hkb)` with `kb : Nat → Nat` and
/// `hkb : ∀ n, BoundedOn (fun r => pow r n) zero R (kb n)` --
/// `CReal.hasDerivative_pow`'s first Skolem hypothesis, computed rather than
/// hand-derived. See this section's own header.
fn pow_bounded_skolem(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    nat: ExprId,
    zero_c: ExprId,
    r_c: ExprId,
    hab0: ExprId,
    pow_uc: ExprId,
) -> (ExprId, ExprId) {
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let n_id = fvar_id(d, n);
    let pow_n_fn = pow_base_fn(d, p, carrier, n);
    let huc = d.apply(pow_uc, &[n]);
    let (k_at_n, proof_at_n) =
        bounded_via_uc(d, p, pow_n_fn, zero_c, r_c, huc, hab0, &[(n_id, nat)]);
    let kb = d.lam_fv(n_fv, nat, k_at_n);
    let hkb = d.lam_fv(n_fv, nat, proof_at_n);
    (kb, hkb)
}

/// `(kd, hkd)` with
/// `hkd : ∀ n, BoundedOn (fun x => mul (ofNat (succ n)) (pow x n)) zero R (kd n)`
/// -- `CReal.hasDerivative_pow`'s second Skolem hypothesis. The uniform
/// continuity of the product comes from `CReal.uniformly_continuous_mul` at
/// the constant `ofNat (succ n)` and [`pow_uc_fn`] at `n`, exactly
/// [`cos_fn_term_uc`]'s own shape one coefficient over.
fn pow_deriv_bounded_skolem(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    nat: ExprId,
    zero_c: ExprId,
    r_c: ExprId,
    hab0: ExprId,
    pow_uc: ExprId,
) -> (ExprId, ExprId) {
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let n_id = fvar_id(d, n);
    let free_n = [(n_id, nat)];

    let succ_n = d.succ(n);
    let coeff = d.const_app(p.of_nat, &[succ_n]);
    let const_fn = {
        let pt_fv = d.fresh_fvar();
        d.lam_fv(pt_fv, carrier, coeff)
    };
    let huc_const = d.lemma(p.uniformly_continuous_const, &[coeff, zero_c, r_c]);

    let pow_n_fn = pow_base_fn(d, p, carrier, n);
    let huc_pow = d.apply(pow_uc, &[n]);

    let (k1, hb1) = bounded_via_uc(d, p, const_fn, zero_c, r_c, huc_const, hab0, &free_n);
    let (k2, hb2) = bounded_via_uc(d, p, pow_n_fn, zero_c, r_c, huc_pow, hab0, &free_n);
    let huc_prod = d.lemma(
        p.uniformly_continuous_mul,
        &[
            const_fn, pow_n_fn, zero_c, r_c, huc_const, huc_pow, k1, k2, hb1, hb2,
        ],
    );

    let deriv_fn = pow_deriv_fn(d, p, carrier, n);
    let (k_at_n, proof_at_n) = bounded_via_uc(d, p, deriv_fn, zero_c, r_c, huc_prod, hab0, &free_n);
    let kd = d.lam_fv(n_fv, nat, k_at_n);
    let hkd = d.lam_fv(n_fv, nat, proof_at_n);
    (kd, hkd)
}

/// `CReal.expTermSuccScale : ∀ m, Equiv (mul (ofNat (Nat.succ m)) (expTerm
/// (Nat.succ m))) (expTerm m)` -- `(m+1)·(1/(m+1)!) = 1/m!`.
///
/// **The index-shifted coefficient identity's whole arithmetic content**, and
/// it is one `Rat` normalisation rather than the cross-multiplication
/// battery `creal/trig.rs::exp_term_antitone_rat` needs for the ORDER fact
/// `1/(n+1)! ≤ 1/n!`. `CReal.ofNat n` unfolds to `ofRat (natDivSucc n 0)` =
/// `ofRat (normalize (ofNat n) 1 _)` and `expTerm n` to `ofRat (normalize 1
/// (factorial n) _)`, so both factors are already `Rat.normalize`s:
/// `Rat.normalize_mul_normalize` fuses them into one, and
/// `Rat.normalize_congr` closes `(m+1)·1·m! = 1·(1·(m+1)!)` against
/// `Nat.factorial_succ` alone. `CReal.ofRat_mul` lifts it back.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_exp_term_succ_scale(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let rat = p.rat;
    let np = d.prelude();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let succ_m = d.succ(m);

    // A := natDivSucc (succ m) 0, unfolded: normalize (ofNat (succ m)) (succ 0) _.
    let n_a = d.of_nat(succ_m);
    let zero_nat = d.zero();
    let e_a = d.succ(zero_nat);
    let h_a = one_le_succ(d, zero_nat);
    let a_rat = normalize(d, n_a, e_a, h_a);

    // B := expTerm (succ m), unfolded: normalize (ofNat 1) (factorial (succ m)) _.
    let one_nat = d.num(1);
    let one_int = d.of_nat(one_nat);
    let fac_sm = d.factorial(succ_m);
    let h_b = d.lemma(np.one_le_factorial, &[succ_m]);
    let b_rat = normalize(d, one_int, fac_sm, h_b);

    // step0 : Rat.mul A B = normalize ((ofNat (succ m))*1) ((succ 0)*(succ m)!) _.
    let step0 = d.lemma(
        rat.normalize_mul_normalize,
        &[n_a, e_a, h_a, one_int, fac_sm, h_b],
    );

    let n1 = d.imul(n_a, one_int);
    let d1 = NatOps::mul(d, e_a, fac_sm);
    let h1 = d.lemma(np.one_le_mul, &[e_a, fac_sm, h_a, h_b]);

    let fac_m = d.factorial(m);
    let h_c = d.lemma(np.one_le_factorial, &[m]);
    let c_rat = normalize(d, one_int, fac_m, h_c);

    // The cross-multiplication `normalize_congr` wants, as a `Nat` identity
    // under one shared `Int.ofNat` (`Int.mul (ofNat a) (ofNat b)` ι-reduces
    // to `ofNat (Nat.mul a b)`, so both sides are already in that shape):
    //   ((succ m) * 1) * m!  =  1 * (1 * (succ m)!)
    let lhs_nat = {
        let inner = NatOps::mul(d, succ_m, one_nat);
        NatOps::mul(d, inner, fac_m)
    };
    let rhs_nat = NatOps::mul(d, one_nat, d1);
    let goal_nat = NatOps::mul(d, succ_m, fac_m);

    let hnat = {
        // LHS -> (succ m) * m!
        let mul_one = d.lemma(np.mul_one, &[succ_m]);
        let sm_one = NatOps::mul(d, succ_m, one_nat);
        let left = d.congr(sm_one, succ_m, mul_one, &|d, t| NatOps::mul(d, t, fac_m));
        // RHS -> (succ m) * m!
        let one_mul_outer = d.lemma(np.one_mul, &[d1]);
        let one_mul_inner = d.lemma(np.one_mul, &[fac_sm]);
        let fac_succ = d.lemma(np.factorial_succ, &[m]);
        let fac_m_sm = NatOps::mul(d, fac_m, succ_m);
        let comm = d.lemma(np.mul_comm, &[fac_m, succ_m]);
        let (_, right) = d.chain(
            rhs_nat,
            &[
                (d1, one_mul_outer),
                (fac_sm, one_mul_inner),
                (fac_m_sm, fac_succ),
                (goal_nat, comm),
            ],
        );
        let back = d.symm(rhs_nat, goal_nat, right);
        d.trans(lhs_nat, goal_nat, rhs_nat, left, back)
    };
    let hyp = d.nat_eq_to_int(lhs_nat, rhs_nat, hnat, &|d, t| d.of_nat(t));

    let step1 = d.lemma(rat.normalize_congr, &[n1, d1, h1, one_int, fac_m, h_c, hyp]);

    let prod_rat = rmul_here(d, a_rat, b_rat);
    let q1 = normalize(d, n1, d1, h1);
    // `rchain`, NOT `d.trans`: the `NatOps` `trans`/`chain`/`symm`/`refl`
    // family builds `Eq AxNat` and rejects `Rat` arguments as
    // `TypeMismatch { expected: AxNat, got: Rat }` -- a real rejection this
    // declaration hit on its first `add_declaration`.
    let (_, rat_eq) = rchain(d, prod_rat, &[(q1, step0), (c_rat, step1)]);

    // Lift to `CReal`: `mul (ofRat A) (ofRat B) ~ ofRat (A*B) ~ ofRat C`.
    let embed_a = embed(d, p, a_rat);
    let embed_b = embed(d, p, b_rat);
    let lhs_creal = cmul(d, p, embed_a, embed_b);
    let embed_prod = embed(d, p, prod_rat);
    let embed_c = embed(d, p, c_rat);
    let leg1 = d.lemma(p.of_rat_mul, &[a_rat, b_rat]);
    let leg2 = embed_eq_to_equiv_here(d, p, prod_rat, c_rat, rat_eq);
    let body = d.lemma(p.equiv_trans, &[lhs_creal, embed_prod, embed_c, leg1, leg2]);

    let value = d.lam_fv(m_fv, nat, body);
    let ty = {
        let of_nat_sm = d.const_app(p.of_nat, &[succ_m]);
        let exp_sm = d.const_app(p.exp_term, &[succ_m]);
        let exp_m = d.const_app(p.exp_term, &[m]);
        let lhs = cmul(d, p, of_nat_sm, exp_sm);
        let stmt = equiv(d, p, lhs, exp_m);
        d.pi_fv(m_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_term_succ_scale,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.cosFnTermDerivCoeff : ∀ j, Equiv (mul (cosTerm (Nat.succ j))
/// (ofNat (Nat.succ (Nat.add (Nat.add j j) 1)))) (neg (sinTerm j))` -- the
/// index-shifted coefficient identity `cosTerm (j+1)·(2j+2) ~ −sinTerm j`.
///
/// Two ingredients and nothing else: [`declare_exp_term_succ_scale`] at
/// `m := 2j+1`, and `(-1)^(j+1) ~ -(-1)^j` (which is `pow`'s own ι-reduction
/// `pow x (succ j) ≡ mul (pow x j) x` plus `mul_neg_equiv`/`mul_one`, no
/// parity lemma). The ONE transport is `Nat.succ_add` moving `cosTerm (succ
/// j)`'s own exponent `Nat.add (succ j) (succ j)` to `Nat.succ (2j+1)`; the
/// two are propositionally but not definitionally equal, since `Nat.add`
/// recurses on the RIGHT and both sides are stuck on a symbolic `j`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_fn_term_deriv_coeff(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let np = d.prelude();

    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let succ_j = d.succ(j);

    let odd = odd_index(d, j); // 2j+1, `sinFnTerm`/`sinTerm`'s own index
    let s_idx = d.succ(odd); // 2j+2
    let add_sj_sj = d.add(succ_j, succ_j);

    // hidx : Nat.add (succ j) (succ j) = Nat.succ (2j+1). Both sides reduce
    // one ι-step to `succ _`, and `Nat.succ_add j j` closes the residue.
    let hidx = {
        let succ_add = d.lemma(np.succ_add, &[j, j]);
        let add_sj_j = d.add(succ_j, j);
        let two_j = d.add(j, j);
        let succ_two_j = d.succ(two_j);
        d.congr(add_sj_j, succ_two_j, succ_add, &|d, t| d.succ(t))
    };

    let neg_one = {
        let one_cc = one_c(d, p);
        cneg(d, p, one_cc)
    };
    let q = cpow(d, p, neg_one, j); // (-1)^j
    let p1 = cpow(d, p, neg_one, succ_j); // (-1)^(j+1)
    let exp_s = d.const_app(p.exp_term, &[s_idx]);
    let exp_odd = d.const_app(p.exp_term, &[odd]);
    let coeff = d.const_app(p.of_nat, &[s_idx]);
    let sin_term_j = {
        let st = d.kernel().const_(p.sin_term, vec![]);
        d.apply(st, &[j])
    };
    let neg_sin = cneg(d, p, sin_term_j);

    // start := ((-1)^(j+1) * expTerm (2j+2)) * ofNat (2j+2)
    let inner = cmul(d, p, p1, exp_s);
    let start = cmul(d, p, inner, coeff);

    // 1. mul_assoc.
    let exp_s_coeff = cmul(d, p, exp_s, coeff);
    let assoc_target = cmul(d, p, p1, exp_s_coeff);
    let h_assoc = d.lemma(p.mul_assoc, &[p1, exp_s, coeff]);

    // 2. commute, then `expTermSuccScale`.
    let coeff_exp_s = cmul(d, p, coeff, exp_s);
    let h_comm = d.lemma(p.mul_comm, &[exp_s, coeff]);
    let h_scale = d.lemma(p.exp_term_succ_scale, &[odd]);
    let refl_p1 = erefl(d, p, p1);
    let step_comm = d.lemma(
        p.mul_congr,
        &[p1, p1, exp_s_coeff, coeff_exp_s, refl_p1, h_comm],
    );
    let p1_coeff_exp = cmul(d, p, p1, coeff_exp_s);
    let step_scale = d.lemma(
        p.mul_congr,
        &[p1, p1, coeff_exp_s, exp_odd, refl_p1, h_scale],
    );
    let p1_exp_odd = cmul(d, p, p1, exp_odd);

    // 3. (-1)^(j+1) ~ -(-1)^j, at the ι-reduced form `mul q (neg one)`.
    let q_neg_one = cmul(d, p, q, neg_one);
    let hqn = {
        let one_cc = one_c(d, p);
        let q_one = cmul(d, p, q, one_cc);
        let neg_q_one = cneg(d, p, q_one);
        let neg_q_inner = cneg(d, p, q);
        let leg1 = mul_neg_equiv(d, p, q, one_cc);
        let mo = d.lemma(p.mul_one, &[q]);
        let leg2 = d.lemma(p.neg_congr, &[q_one, q, mo]);
        echain(d, p, q_neg_one, &[(neg_q_one, leg1), (neg_q_inner, leg2)])
    };
    let neg_q = cneg(d, p, q);
    let refl_exp_odd = erefl(d, p, exp_odd);
    let step_sign = d.lemma(
        p.mul_congr,
        &[q_neg_one, neg_q, exp_odd, exp_odd, hqn, refl_exp_odd],
    );
    let neg_q_exp = cmul(d, p, neg_q, exp_odd);
    let step_pull = neg_mul_equiv_left(d, p, q, exp_odd);

    let proof_at_s = echain(
        d,
        p,
        start,
        &[
            (assoc_target, h_assoc),
            (p1_coeff_exp, step_comm),
            (p1_exp_odd, step_scale),
            (neg_q_exp, step_sign),
            (neg_sin, step_pull),
        ],
    );

    // Transport the exponent back to `cosTerm (succ j)`'s own shape.
    let back = d.symm(add_sj_sj, s_idx, hidx);
    let body = d.nat_rewrite(s_idx, add_sj_sj, back, proof_at_s, &|d, t| {
        let exp_t = d.const_app(p.exp_term, &[t]);
        let inner_t = cmul(d, p, p1, exp_t);
        let lhs_t = cmul(d, p, inner_t, coeff);
        equiv(d, p, lhs_t, neg_sin)
    });

    let value = d.lam_fv(j_fv, nat, body);
    let ty = {
        let ct = d.kernel().const_(p.cos_term, vec![]);
        let cos_term_sj = d.apply(ct, &[succ_j]);
        let lhs = cmul(d, p, cos_term_sj, coeff);
        let stmt = equiv(d, p, lhs, neg_sin);
        d.pi_fv(j_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_term_deriv_coeff,
        uparams: vec![],
        ty,
        value,
    })
}

/// `∀ x, le zero x → le x R → <body x>` -- the pointwise-agreement hypothesis
/// `CReal.hasDerivative_congr` takes. The two range hypotheses are bound and
/// discarded: every agreement proof in this section is an unconditional
/// algebraic identity, `hasDerivative_congr` merely does not need it to be.
fn agree_lam(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    zero_c: ExprId,
    r_c: ExprId,
    body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hax_fv = d.fresh_fvar();
    let hxb_fv = d.fresh_fvar();
    let inner = body(d, x);
    let range_ax = cle(d, p, zero_c, x);
    let range_xb = cle(d, p, x, r_c);
    let with_hxb = d.lam_fv(hxb_fv, range_xb, inner);
    let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
    d.lam_fv(x_fv, carrier, with_hax)
}

/// `CReal.cosFnTermHasDerivative : ∀ j, HasDerivativeOn (fun x => cosFnTerm
/// (Nat.succ j) x) (fun x => neg (sinFnTerm j x)) zero R`.
///
/// `hasDerivative_pow` at `n := 2j+1` (so the FUNCTION's exponent is `2j+2`,
/// never a `Nat.sub`), then `hasDerivative_smul` at `c := cosTerm (succ j)`
/// whose magnitude bound is read off `bounded_of_uniformly_continuous`
/// applied to the CONSTANT function `fun _ => c` and unfolded at the single
/// point `zero` -- no `cosTermAbsLeDominant` arithmetic is needed, since any
/// bound at all suffices for `smul`. `hasDerivative_congr` then moves both
/// sides into the named `cosFnTerm`/`sinFnTerm` shapes: the function side by
/// the `Nat.succ_add` index transport, the derivative side by
/// [`declare_cos_fn_term_deriv_coeff`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_fn_term_has_derivative(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let np = d.prelude();
    let zero_c = czero(d, p);
    let r_c = r_domain(d, p);
    let hab0 = hab_zero_r(d, p);

    let pow_uc = pow_uc_fn(d, p, carrier, nat, zero_c, r_c, hab0);
    let (kb, hkb) = pow_bounded_skolem(d, p, carrier, nat, zero_c, r_c, hab0, pow_uc);
    let (kd, hkd) = pow_deriv_bounded_skolem(d, p, carrier, nat, zero_c, r_c, hab0, pow_uc);

    let id_fn = {
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        d.lam_fv(pt_fv, carrier, pt)
    };
    let huc_id = d.lemma(p.uniformly_continuous_id, &[zero_c, r_c]);
    let (k1, hb_id) = bounded_via_uc(d, p, id_fn, zero_c, r_c, huc_id, hab0, &[]);

    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let j_id = fvar_id(d, j);
    let succ_j = d.succ(j);
    let odd = odd_index(d, j);
    let s_idx = d.succ(odd);
    let add_sj_sj = d.add(succ_j, succ_j);

    let hd_pow = d.const_app(
        p.has_derivative_pow,
        &[zero_c, r_c, k1, hb_id, kb, kd, hkb, hkd, odd],
    );
    let pow_fn = pow_succ_fn(d, p, carrier, odd);
    let deriv_fn = pow_deriv_fn(d, p, carrier, odd);

    let cos_term_sj = {
        let ct = d.kernel().const_(p.cos_term, vec![]);
        d.apply(ct, &[succ_j])
    };
    let const_fn = {
        let pt_fv = d.fresh_fvar();
        d.lam_fv(pt_fv, carrier, cos_term_sj)
    };
    let huc_const = d.lemma(p.uniformly_continuous_const, &[cos_term_sj, zero_c, r_c]);
    let (kc, hbc) = bounded_via_uc(d, p, const_fn, zero_c, r_c, huc_const, hab0, &[(j_id, nat)]);
    let hz = d.lemma(p.le_refl, &[zero_c]);
    let hbound = d.lemma(
        p.bounded_on_unfold,
        &[const_fn, zero_c, r_c, kc, hbc, zero_c, hz, hab0],
    );

    let smul_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let pr = cpow(d, p, r, s_idx);
        let body = cmul(d, p, cos_term_sj, pr);
        d.lam_fv(r_fv, carrier, body)
    };
    let smul_deriv_fn = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let coeff = d.const_app(p.of_nat, &[s_idx]);
        let px = cpow(d, p, x, odd);
        let inner = cmul(d, p, coeff, px);
        let body = cmul(d, p, cos_term_sj, inner);
        d.lam_fv(x_fv, carrier, body)
    };
    let hd_smul = d.lemma(
        p.has_derivative_smul,
        &[
            cos_term_sj,
            pow_fn,
            deriv_fn,
            zero_c,
            r_c,
            hd_pow,
            kc,
            hbound,
        ],
    );

    // Target shapes.
    let g_fn = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = d.const_app(p.cos_fn_term, &[succ_j, x]);
        d.lam_fv(x_fv, carrier, body)
    };
    let gp_fn = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let sft = d.const_app(p.sin_fn_term, &[j, x]);
        let body = cneg(d, p, sft);
        d.lam_fv(x_fv, carrier, body)
    };

    // agree_g : Equiv (cosFnTerm (succ j) x) (cos_term_sj * pow x (2j+2)).
    let hidx = {
        let succ_add = d.lemma(np.succ_add, &[j, j]);
        let add_sj_j = d.add(succ_j, j);
        let two_j = d.add(j, j);
        let succ_two_j = d.succ(two_j);
        d.congr(add_sj_j, succ_two_j, succ_add, &|d, t| d.succ(t))
    };
    let back = d.symm(add_sj_sj, s_idx, hidx);
    let agree_g = agree_lam(d, p, carrier, zero_c, r_c, &|d, x| {
        let target = {
            let pr = cpow(d, p, x, s_idx);
            cmul(d, p, cos_term_sj, pr)
        };
        let refl = erefl(d, p, target);
        d.nat_rewrite(s_idx, add_sj_sj, back, refl, &|d, t| {
            let pr = cpow(d, p, x, t);
            let lhs = cmul(d, p, cos_term_sj, pr);
            equiv(d, p, lhs, target)
        })
    });

    // agree_gp : Equiv (neg (sinFnTerm j x)) (cos_term_sj * (ofNat (2j+2) * pow x (2j+1))).
    let coeff_c = d.const_app(p.of_nat, &[s_idx]);
    let sin_term_j = {
        let st = d.kernel().const_(p.sin_term, vec![]);
        d.apply(st, &[j])
    };
    let h_coeff = d.lemma(p.cos_fn_term_deriv_coeff, &[j]);
    let agree_gp = agree_lam(d, p, carrier, zero_c, r_c, &|d, x| {
        let px = cpow(d, p, x, odd);
        let inner = cmul(d, p, coeff_c, px);
        let rhs = cmul(d, p, cos_term_sj, inner);
        let ct_coeff = cmul(d, p, cos_term_sj, coeff_c);
        let regrouped = cmul(d, p, ct_coeff, px);
        let h_assoc = d.lemma(p.mul_assoc, &[cos_term_sj, coeff_c, px]);
        let un_assoc = esymm(d, p, regrouped, rhs, h_assoc);
        let neg_sin = cneg(d, p, sin_term_j);
        let refl_px = erefl(d, p, px);
        let h_sub = d.lemma(p.mul_congr, &[ct_coeff, neg_sin, px, px, h_coeff, refl_px]);
        let neg_sin_px = cmul(d, p, neg_sin, px);
        let h_pull = neg_mul_equiv_left(d, p, sin_term_j, px);
        let sin_px = cmul(d, p, sin_term_j, px);
        let neg_prod = cneg(d, p, sin_px);
        let forward = echain(
            d,
            p,
            rhs,
            &[
                (regrouped, un_assoc),
                (neg_sin_px, h_sub),
                (neg_prod, h_pull),
            ],
        );
        esymm(d, p, rhs, neg_prod, forward)
    });

    let body = d.lemma(
        p.has_derivative_congr,
        &[
            smul_fn,
            smul_deriv_fn,
            zero_c,
            r_c,
            hd_smul,
            g_fn,
            gp_fn,
            agree_g,
            agree_gp,
        ],
    );

    let value = d.lam_fv(j_fv, nat, body);
    let ty = {
        let stmt = hd_ty(d, p, g_fn, gp_fn, zero_c, r_c);
        d.pi_fv(j_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_term_has_derivative,
        uparams: vec![],
        ty,
        value,
    })
}

/// `fun x => sumRange (fun k => cosFnTerm k x) m`, at a fixed `m`.
fn cos_partial_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    nat: ExprId,
    m: ExprId,
) -> ExprId {
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let f_pt = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.cos_fn_term, &[k, pt]);
        d.lam_fv(k_fv, nat, body)
    };
    let body = d.const_app(p.sum_range, &[f_pt, m]);
    d.lam_fv(pt_fv, carrier, body)
}

/// `fun x => neg (sumRange (fun k => sinFnTerm k x) m)`, at a fixed `m`.
fn neg_sin_partial_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    nat: ExprId,
    m: ExprId,
) -> ExprId {
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let f_pt = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.sin_fn_term, &[k, pt]);
        d.lam_fv(k_fv, nat, body)
    };
    let raw = d.const_app(p.sum_range, &[f_pt, m]);
    let body = cneg(d, p, raw);
    d.lam_fv(pt_fv, carrier, body)
}

/// `CReal.cosFnPartialHasDerivative : ∀ n, HasDerivativeOn (fun x => sumRange
/// (fun k => cosFnTerm k x) (Nat.succ n)) (fun x => neg (sumRange (fun k =>
/// sinFnTerm k x) n)) zero R` -- **lane 159's step 1**.
///
/// Induction on `n` over `CReal.hasDerivative_add`. The `succ n` on the
/// function side against a bare `n` on the derivative side is not an accident
/// of statement: `d/dx cosFnTerm 0` is `0`, so the first `n+1` cosine terms
/// differentiate to the first `n` sine terms, and stating it any other way
/// would need a `Nat.pred`.
///
/// Both cases close through `hasDerivative_congr` for the DERIVATIVE side
/// only -- `sumRange`'s own ι-reduction already makes the function sides
/// definitionally equal (`sumRange f (succ m) ≡ add (sumRange f m) (f m)`),
/// so the function agreement is `equiv_refl` in both. The derivative residues
/// are `Equiv (neg zero) zero` at the base and `Equiv (neg (add A B)) (add
/// (neg A) (neg B))` at the step.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_fn_partial_has_derivative(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let r_c = r_domain(d, p);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let sv = d.succ(v);
        let f = cos_partial_at(d, p, carrier, nat, sv);
        let fp = neg_sin_partial_at(d, p, carrier, nat, v);
        hd_ty(d, p, f, fp, zero_c, r_c)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        // `sumRange f 1 x` ι-reduces to `add zero (cosFnTerm 0 x)`, and
        // `cosFnTerm 0 x ≡ mul (cosTerm 0) (pow x 0) ≡ mul (cosTerm 0) one`
        // -- constant in `x`.
        let zero_nat = d.zero();
        let one_nat = d.num(1);
        let cos_term_0 = {
            let ct = d.kernel().const_(p.cos_term, vec![]);
            d.apply(ct, &[zero_nat])
        };
        let one_cc = one_c(d, p);
        let term0 = cmul(d, p, cos_term_0, one_cc);
        let konst = cadd(d, p, zero_c, term0);
        let const_fn = {
            let pt_fv = d.fresh_fvar();
            d.lam_fv(pt_fv, carrier, konst)
        };
        let zero_fn = {
            let pt_fv = d.fresh_fvar();
            d.lam_fv(pt_fv, carrier, zero_c)
        };
        let hf = d.const_app(p.has_derivative_const, &[konst, zero_c, r_c]);
        let g_fn = cos_partial_at(d, p, carrier, nat, one_nat);
        let gp_fn = neg_sin_partial_at(d, p, carrier, nat, zero_nat);
        let agree_g = agree_lam(d, p, carrier, zero_c, r_c, &|d, _x| erefl(d, p, konst));
        let agree_gp = agree_lam(d, p, carrier, zero_c, r_c, &|d, _x| {
            neg_zero_equiv_here(d, p)
        });
        d.lemma(
            p.has_derivative_congr,
            &[
                const_fn, zero_fn, zero_c, r_c, hf, g_fn, gp_fn, agree_g, agree_gp,
            ],
        )
    };

    let step = |d: &mut IntDev<'_>, jj: ExprId, ih: ExprId| -> ExprId {
        let sj = d.succ(jj);
        let ssj = d.succ(sj);
        let f_prev = cos_partial_at(d, p, carrier, nat, sj);
        let fp_prev = neg_sin_partial_at(d, p, carrier, nat, jj);
        let term_fn = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let body = d.const_app(p.cos_fn_term, &[sj, x]);
            d.lam_fv(x_fv, carrier, body)
        };
        let term_deriv_fn = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let sft = d.const_app(p.sin_fn_term, &[jj, x]);
            let body = cneg(d, p, sft);
            d.lam_fv(x_fv, carrier, body)
        };
        let hterm = d.lemma(p.cos_fn_term_has_derivative, &[jj]);
        let hsum = d.lemma(
            p.has_derivative_add,
            &[
                f_prev,
                fp_prev,
                term_fn,
                term_deriv_fn,
                zero_c,
                r_c,
                ih,
                hterm,
            ],
        );

        let sum_fn = {
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            let a = d.apply(f_prev, &[r]);
            let b = d.apply(term_fn, &[r]);
            let body = cadd(d, p, a, b);
            d.lam_fv(r_fv, carrier, body)
        };
        let sum_deriv_fn = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let a = d.apply(fp_prev, &[x]);
            let b = d.apply(term_deriv_fn, &[x]);
            let body = cadd(d, p, a, b);
            d.lam_fv(x_fv, carrier, body)
        };

        let g_fn = cos_partial_at(d, p, carrier, nat, ssj);
        let gp_fn = neg_sin_partial_at(d, p, carrier, nat, sj);

        let agree_g = agree_lam(d, p, carrier, zero_c, r_c, &|d, x| {
            let a = d.apply(f_prev, &[x]);
            let b = d.apply(term_fn, &[x]);
            let target = cadd(d, p, a, b);
            erefl(d, p, target)
        });
        let agree_gp = agree_lam(d, p, carrier, zero_c, r_c, &|d, x| {
            let f_pt = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let body = d.const_app(p.sin_fn_term, &[k, x]);
                d.lam_fv(k_fv, nat, body)
            };
            let prev = d.const_app(p.sum_range, &[f_pt, jj]);
            let last = d.const_app(p.sin_fn_term, &[jj, x]);
            neg_add_distrib(d, p, prev, last)
        });

        d.lemma(
            p.has_derivative_congr,
            &[
                sum_fn,
                sum_deriv_fn,
                zero_c,
                r_c,
                hsum,
                g_fn,
                gp_fn,
                agree_g,
                agree_gp,
            ],
        )
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let at_n = induct_ty(d, &motive, &base, &step, n);
    let value = d.lam_fv(n_fv, nat, at_n);
    let ty = {
        let stmt = motive(d, n);
        d.pi_fv(n_fv, nat, stmt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_partial_has_derivative,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit the per-term and partial-sum derivative facts for `cosFnWide` --
/// lane 159's step 1, plus the two coefficient lemmas underneath it.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_fn_derivative(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_exp_term_succ_scale(d, p)?;
    declare_cos_fn_term_deriv_coeff(d, p)?;
    declare_cos_fn_term_has_derivative(d, p)?;
    declare_cos_fn_partial_has_derivative(d, p)
}

// ============================================================================
// From the partial sums to `cosFnWide` itself (lane 159 step 3)
// ============================================================================
//
// `CReal.hasDerivative_uniform_limit` takes `F`, `F'`, `G`, `G'` with a
// per-index `HasDerivativeOn (F n) (F' n)` and BOTH uniform convergences.
// [`declare_cos_fn_partial_has_derivative`] supplies the per-index fact at
// `F n := Sₙ₊₁` and `F' n := −Tₙ`, so the two convergence witnesses this
// file already has have to be re-indexed to match:
//
//   * `cosFnWideUniformConverges` is about `Sₙ`, not `Sₙ₊₁`
//     ([`declare_uniform_converges_shift`]), and
//   * `sinFnUniformConverges` is about `Tₙ`, not `−Tₙ`
//     ([`declare_uniform_converges_neg`]).
//
// **The shift is the one that costs something, and it is NOT free from
// `rat_prelude` as it stands.** `UniformConvergesOn`'s spec bounds the error
// at index `n` by `natDivSucc rate n`; the shifted family's error at `n` is
// the original's at `succ n`, bounded by the strictly TIGHTER `natDivSucc
// rate (succ n)`, and weakening that back to `natDivSucc rate n` is one-step
// antitonicity of `natDivSucc` in its INDEX at a SYMBOLIC numerator.
// `Rat.natDivSucc_antitone` is stated at numerator `1` only, and
// `Rat.natDivSucc_le_scaled` reads a `(c+1)·n + c`-shaped index back to `n` —
// `succ n` is not of that shape for any `c` that leaves a bound shrinking in
// `n`. [`declare_nat_div_succ_step_le`] closes it without touching
// `rat_prelude`: `Rat.natDivSucc_mul` factors `natDivSucc k j` as
// `natDivSucc k 0 · natDivSucc 1 j`, the numerator-`1` antitonicity applies
// to the second factor, and `Rat.mul_le_mul_of_nonneg_left` scales it back.

/// `Rat.natDivSucc k j`, local to this section (mirrors
/// `convergence::div_succ_at`, which this file already imports).
fn ndsucc(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    div_succ_at(d, p, k, j)
}

/// `CReal.natDivSuccStepLe : ∀ (k n : Nat), Rat.le (Rat.natDivSucc k
/// (Nat.succ n)) (Rat.natDivSucc k n)` — one-step antitonicity of
/// `Rat.natDivSucc` in its INDEX, at a **symbolic numerator**.
///
/// `RatPrelude::nat_div_succ_antitone` is the same statement at numerator
/// `1`, and its own doc comment records how long that one cost; this needs no
/// new cross-multiplication at all. `RatPrelude::nat_div_succ_mul` factors
/// `natDivSucc (k·1) j` as `natDivSucc k 0 · natDivSucc 1 j`, so the index
/// lives entirely in the second factor, where numerator-`1` antitonicity
/// already applies, and `Rat.mul_le_mul_of_nonneg_left` (the first factor is
/// nonnegative by `Rat.zero_le_natDivSucc`) scales the comparison back up.
/// `Nat.mul_one` retires the `k·1`.
///
/// Declared here rather than in `rat_prelude` because that module is another
/// lane's; it belongs there, and the `CReal.` namespace is a holding pen.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_nat_div_succ_step_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let rat = p.rat;
    let np = d.prelude();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let succ_n = d.succ(n);

    let one_nat = d.num(1);
    let zero_nat = d.zero();
    let k_times_one = NatOps::mul(d, k, one_nat);

    let head = ndsucc(d, p, k, zero_nat); // natDivSucc k 0
    let tail_succ = ndsucc(d, p, one_nat, succ_n); // natDivSucc 1 (succ n)
    let tail_n = ndsucc(d, p, one_nat, n); // natDivSucc 1 n

    let hle_nat = d.lemma(np.le_succ, &[n]);
    let hant = d.lemma(rat.nat_div_succ_antitone, &[n, succ_n, hle_nat]);
    // hant : Rat.le tail_succ tail_n

    let hk_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[k, zero_nat]);
    let hscaled = d.lemma(
        rat.mul_le_mul_of_nonneg_left,
        &[head, tail_succ, tail_n, hk_nonneg, hant],
    );
    // hscaled : Rat.le (head * tail_succ) (head * tail_n)

    let prod_succ = crate::rat_prelude::ops::rmul(d, head, tail_succ);
    let prod_n = crate::rat_prelude::ops::rmul(d, head, tail_n);
    let fused_succ = ndsucc(d, p, k_times_one, succ_n);
    let fused_n = ndsucc(d, p, k_times_one, n);

    let e1 = d.lemma(rat.nat_div_succ_mul, &[k, one_nat, succ_n]);
    let e2 = d.lemma(rat.nat_div_succ_mul, &[k, one_nat, n]);

    let after_lhs = rat_eq_rewrite(d, prod_succ, fused_succ, e1, hscaled, &|d, t| {
        crate::rat_prelude::ops::rle(d, rat, t, prod_n)
    });
    let after_rhs = rat_eq_rewrite(d, prod_n, fused_n, e2, after_lhs, &|d, t| {
        crate::rat_prelude::ops::rle(d, rat, fused_succ, t)
    });
    // after_rhs : Rat.le (natDivSucc (k*1) (succ n)) (natDivSucc (k*1) n)

    let hmul_one = d.lemma(np.mul_one, &[k]);
    let body = d.nat_rewrite(k_times_one, k, hmul_one, after_rhs, &|d, t| {
        let lhs = ndsucc(d, p, t, succ_n);
        let rhs = ndsucc(d, p, t, n);
        crate::rat_prelude::ops::rle(d, rat, lhs, rhs)
    });

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(k_fv, nat, with_n)
    };
    let ty = {
        let lhs = ndsucc(d, p, k, succ_n);
        let rhs = ndsucc(d, p, k, n);
        let stmt = crate::rat_prelude::ops::rle(d, rat, lhs, rhs);
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(k_fv, nat, with_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.nat_div_succ_step_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Nat → CReal → CReal`.
fn seq_fn_ty_here(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let inner = d.arrow(carrier, carrier);
    d.arrow(nat, inner)
}

/// `CReal.uniformConvergesShift : ∀ F G a b, UniformConvergesOn F G a b →
/// UniformConvergesOn (fun n => F (Nat.succ n)) G a b`.
///
/// The rate is unchanged; the whole content is
/// [`declare_nat_div_succ_step_le`] weakening the shifted family's own
/// (tighter) bound at `succ n` back to `natDivSucc rate n`. See this
/// section's header for why that step is not free.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_uniform_converges_shift(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let seq_ty = seq_fn_ty_here(d, p);
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hu_ty = d.const_app(p.uniform_converges_on, &[f, g, a, b]);
    let hu_fv = d.fresh_fvar();
    let hu = d.kernel().fvar(hu_fv);

    let shifted = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let body = d.apply(f, &[sn]);
        d.lam_fv(n_fv, nat, body)
    };

    let rate = d.const_app(p.uconv_rate, &[f, g, a, b, hu]);
    let huspec = d.const_app(p.uconv_spec, &[f, g, a, b, hu]);

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);

        let sn = d.succ(n);
        let tight = d.apply(huspec, &[sn, x, hax, hxb]);
        let fsnx = d.apply(f, &[sn, x]);
        let gx = d.apply(g, &[x]);

        let q_tight = ndsucc(d, p, rate, sn);
        let q_loose = ndsucc(d, p, rate, n);
        let hq = d.lemma(p.nat_div_succ_step_le, &[rate, n]);
        let hembed = d.lemma(p.of_rat_le, &[q_tight, q_loose, hq]);

        let ny = cneg(d, p, gx);
        let diff = cadd(d, p, fsnx, ny);
        let magnitude = cabs(d, p, diff);
        let e_tight = embed(d, p, q_tight);
        let e_loose = embed(d, p, q_loose);
        let widened = d.lemma(p.le_trans, &[magnitude, e_tight, e_loose, tight, hembed]);

        let range_xb = cle(d, p, x, b);
        let range_ax = cle(d, p, a, x);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, widened);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_x = d.lam_fv(x_fv, carrier, with_hax);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uconv_mk, &[shifted, g, a, b, rate, spec]);

    let value = {
        let with_hu = d.lam_fv(hu_fv, hu_ty, mk_applied);
        let with_b = d.lam_fv(b_fv, carrier, with_hu);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_g = d.lam_fv(g_fv, func_ty, with_a);
        d.lam_fv(f_fv, seq_ty, with_g)
    };
    let ty = {
        let conclusion = d.const_app(p.uniform_converges_on, &[shifted, g, a, b]);
        let after_hu = d.arrow(hu_ty, conclusion);
        let with_b = d.pi_fv(b_fv, carrier, after_hu);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, seq_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniform_converges_shift,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.uniformConvergesNeg : ∀ F G a b, UniformConvergesOn F G a b →
/// UniformConvergesOn (fun n x => neg (F n x)) (fun x => neg (G x)) a b`.
///
/// The rate and every bound are unchanged: `|(−u) − (−v)| = |−(u − v)|` and
/// `le_abs_neg_of_le_abs` (`creal/derivative.rs`) bounds a negation by
/// whatever bounds the original **without deciding a sign** — `abs` is not
/// `Equiv`-invariant under `neg`, so this is not a congruence. The only
/// algebra is `neg_add_distrib` moving `neg (u + (−v))` to `(−u) + (−(−v))`,
/// the shape `close_within (neg u) (neg v)` literally is.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_uniform_converges_neg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let seq_ty = seq_fn_ty_here(d, p);
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hu_ty = d.const_app(p.uniform_converges_on, &[f, g, a, b]);
    let hu_fv = d.fresh_fvar();
    let hu = d.kernel().fvar(hu_fv);

    let neg_seq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fnx = d.apply(f, &[n, x]);
        let body = cneg(d, p, fnx);
        let with_x = d.lam_fv(x_fv, carrier, body);
        d.lam_fv(n_fv, nat, with_x)
    };
    let neg_fn = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let gx = d.apply(g, &[x]);
        let body = cneg(d, p, gx);
        d.lam_fv(x_fv, carrier, body)
    };

    let rate = d.const_app(p.uconv_rate, &[f, g, a, b, hu]);
    let huspec = d.const_app(p.uconv_spec, &[f, g, a, b, hu]);

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);

        let base = d.apply(huspec, &[n, x, hax, hxb]);
        let fnx = d.apply(f, &[n, x]);
        let gx = d.apply(g, &[x]);
        let q = ndsucc(d, p, rate, n);
        let bound = embed(d, p, q);

        let ngx = cneg(d, p, gx);
        let t = cadd(d, p, fnx, ngx);
        let neg_t = cneg(d, p, t);
        let neg_bounded = le_abs_neg_of_le_abs(d, p, t, bound, base);
        // neg_bounded : le (abs (neg t)) bound

        let nfnx = cneg(d, p, fnx);
        let nngx = cneg(d, p, ngx);
        let target = cadd(d, p, nfnx, nngx);
        let distrib = neg_add_distrib(d, p, fnx, ngx);
        // distrib : Equiv (neg t) target
        let flipped = esymm(d, p, neg_t, target, distrib);
        // flipped : Equiv target (neg t)
        let out = abs_le_of_equiv(d, p, target, neg_t, bound, flipped, neg_bounded);

        let range_xb = cle(d, p, x, b);
        let range_ax = cle(d, p, a, x);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, out);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_x = d.lam_fv(x_fv, carrier, with_hax);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uconv_mk, &[neg_seq, neg_fn, a, b, rate, spec]);

    let value = {
        let with_hu = d.lam_fv(hu_fv, hu_ty, mk_applied);
        let with_b = d.lam_fv(b_fv, carrier, with_hu);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_g = d.lam_fv(g_fv, func_ty, with_a);
        d.lam_fv(f_fv, seq_ty, with_g)
    };
    let ty = {
        let conclusion = d.const_app(p.uniform_converges_on, &[neg_seq, neg_fn, a, b]);
        let after_hu = d.arrow(hu_ty, conclusion);
        let with_b = d.pi_fv(b_fv, carrier, after_hu);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, seq_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniform_converges_neg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.cosFnWideHasDerivative : HasDerivativeOn cosFnWide (fun x => neg
/// (sinFn x)) zero (ofRat (natDivSucc 8 4))` -- **the target**: cosine
/// differentiates to minus sine on `[0, 8/5]`.
///
/// `CReal.hasDerivative_uniform_limit` at `F n := Sₙ₊₁`, `F' n := −Tₙ`, with
/// the two re-indexed convergence witnesses
/// ([`declare_uniform_converges_shift`], [`declare_uniform_converges_neg`])
/// and [`declare_cos_fn_partial_has_derivative`] as the per-index
/// hypothesis. Nothing new is proved here; every part was built above.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_cos_fn_wide_has_derivative(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let r_c = r_domain(d, p);

    let cos_seq = cos_fn_partial_sums_fn(d, p, carrier, nat);
    let cos_g = d.kernel().const_(p.cos_fn_wide, vec![]);
    let hu_cos = d.kernel().const_(p.cos_fn_wide_uniform_converges, vec![]);
    let hu_cos_shift = d.lemma(
        p.uniform_converges_shift,
        &[cos_seq, cos_g, zero_c, r_c, hu_cos],
    );
    let shifted_seq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let body = d.apply(cos_seq, &[sn]);
        d.lam_fv(n_fv, nat, body)
    };

    let sin_seq = sin_fn_partial_sums_fn(d, p, carrier, nat);
    let sin_g = d.kernel().const_(p.sin_fn, vec![]);
    let hu_sin = d.kernel().const_(p.sin_fn_uniform_converges, vec![]);
    let hu_sin_neg = d.lemma(
        p.uniform_converges_neg,
        &[sin_seq, sin_g, zero_c, r_c, hu_sin],
    );
    let neg_sin_seq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fnx = d.apply(sin_seq, &[n, x]);
        let body = cneg(d, p, fnx);
        let with_x = d.lam_fv(x_fv, carrier, body);
        d.lam_fv(n_fv, nat, with_x)
    };
    let neg_sin_fn = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let gx = d.apply(sin_g, &[x]);
        let body = cneg(d, p, gx);
        d.lam_fv(x_fv, carrier, body)
    };

    let hd_all = d.kernel().const_(p.cos_fn_partial_has_derivative, vec![]);

    let value = d.lemma(
        p.has_derivative_uniform_limit,
        &[
            shifted_seq,
            neg_sin_seq,
            cos_g,
            neg_sin_fn,
            zero_c,
            r_c,
            hd_all,
            hu_cos_shift,
            hu_sin_neg,
        ],
    );
    let ty = hd_ty(d, p, cos_g, neg_sin_fn, zero_c, r_c);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_wide_has_derivative,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit the two `UniformConvergesOn` re-indexings and the target,
/// `CReal.cosFnWideHasDerivative`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_fn_wide_derivative(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_nat_div_succ_step_le(d, p)?;
    declare_uniform_converges_shift(d, p)?;
    declare_uniform_converges_neg(d, p)?;
    declare_cos_fn_wide_has_derivative(d, p)
}
