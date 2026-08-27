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
use crate::rat_prelude::ops::{one_le_succ, radd, rat_eq_rewrite};
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

/// Admit `CReal.cosFn_one_equiv_cosOne : Equiv (cosFn one) cosOne`. Mirrors
/// `creal/exp_fn.rs::declare_exp_fn_equiv_e` step for step: eliminate
/// `CReal.cosOneConverges`'s `Exists` witness into a per-`n` `Within` fact,
/// bridge it to `close_within` via [`close_within_of_within_at`] (leg 1),
/// transport `CReal.cosFnUniformConverges`'s own `.spec` at `x := one` from
/// `cosFnTerm j one` to `cosTerm j` via [`cos_fn_term_one_equiv`] +
/// `CReal.sumRange_congr` (leg 2), combine the two legs by the triangle
/// inequality ([`combine_two_legs`]), and close with
/// `CReal.equiv_zero_of_rate` + [`equiv_of_sub_equiv_zero`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_fn_equiv_cos_one(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let one_cc = one_c(d, p);
    let cos_one_const = d.kernel().const_(p.cos_one, vec![]);
    let cos_term_c = d.kernel().const_(p.cos_term, vec![]);
    let cos_series_partial_c = d.kernel().const_(p.cos_series_partial, vec![]);

    // Peel `F`/`G`/`a`/`b` off `cosFnUniformConverges`'s own INFERRED type,
    // rather than reconstructing `big_f` by hand — guarantees an exact match
    // with the declared theorem's actual ascribed type.
    let u_conv = d.kernel().const_(p.cos_fn_uniform_converges, vec![]);
    let ty_u = d.kernel().infer(u_conv)?;
    let (inner1, b_u) = unapp(d, ty_u);
    let (inner2, a_u) = unapp(d, inner1);
    let (inner3, g_u) = unapp(d, inner2);
    let (_, f_u) = unapp(d, inner3);
    let uconv_rate_val = d.const_app(p.uconv_rate, &[f_u, g_u, a_u, b_u, u_conv]);
    let uconv_spec_val = d.const_app(p.uconv_spec, &[f_u, g_u, a_u, b_u, u_conv]);

    let hab_lo = zero_le_one(d, p);
    let hab_hi = d.lemma(p.le_refl, &[one_cc]);

    let g_one = d.apply(g_u, &[one_cc]); // cosFn one
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

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_fn_one_equiv_cos_one,
        uparams: vec![],
        ty: target,
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

    // --- nested induction: `pow` uniform continuity, symbolic exponent ---
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
    let pow_uc = d.lam_fv(m_fv, nat, pow_uc_at_m);
    // pow_uc : ∀ m, UniformlyContinuousOn (fun pt => pow pt m) zero R.

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
