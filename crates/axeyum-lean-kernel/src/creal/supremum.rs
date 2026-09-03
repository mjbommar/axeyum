//! `CReal.maxRange`, the finite-mesh-maximum primitive for the LUB family's
//! honest row 1 (Spivak ch. 8): the supremum of a uniformly continuous
//! function on a compact interval.
//!
//! See
//! [`docs/research/11-design-review/2026-08-27-locatedness-and-the-measure-theoretic-lesson.md`](../../../../../docs/research/11-design-review/2026-08-27-locatedness-and-the-measure-theoretic-lesson.md)
//! §4 for the assignment this file answers, and its own §2 for **why this is
//! constructive at all**: `sup` for a general bounded set needs
//! **locatedness** (a computable distance function) and is NOT available
//! here — that is why Bishop completeness, not a general LUB, is what this
//! kernel ships. A uniformly continuous function on `[a, b]` is different:
//! its mesh maxima converge (this file), because the modulus itself supplies
//! the missing locatedness.
//!
//! ## The value/argmax distinction — read this before using anything here
//!
//! **The supremum VALUE of a uniformly continuous `F` on `[a, b]` is
//! constructive. The ARGMAX is not, and never will be with the tools this
//! kernel has.**
//! [`CReal.evt_attained_max_decides_sign`](super::ExtremeValueNames::evt_attained_max_decides_sign)
//! (`creal/extreme_value.rs`) proves that an *attaining* maximiser for a
//! specific uniformly continuous family would decide the sign of an
//! arbitrary real — i.e. attainment is EVT's row 2, and it is a genuine
//! impossibility result, not an unfinished proof. `CReal.maxRange` and
//! everything built on it here only ever produce a *value*: the height of
//! the graph, never a point that reaches it. Anyone tempted to add an
//! `argmax`-shaped declaration to this file should read that theorem's own
//! module documentation first (`creal/extreme_value.rs`).
//!
//! ## What this file lands, and what it does not
//!
//! **STALE BELOW THIS LINE.** `CReal.supOn` landed on 2026-08-30; every
//! paragraph between here and the "`CReal.supOn` LANDED" section is the
//! incident history of getting there, kept because its diagnoses are correct
//! and reusable, but its account of what REMAINS is superseded. Read that
//! section first.
//!
//! **Landed**: `CReal.maxRange`, a `Nat.rec`-structured finite-mesh-maximum
//! fold over an arbitrary `Nat → CReal` sequence — the `max`-lattice analogue
//! of [`CReal.sumRange`](super::CRealPrelude::sum_range) — plus its defining
//! equations and the two order facts every consumer of a finite maximum
//! needs: every sampled value is `≤` the fold (`maxRange_self_le`, hence
//! `maxRange_ub` at any earlier index via `maxRange_mono`), and the fold is
//! monotone in its own bound (`maxRange_mono`, built from
//! [`CReal.mono_of_le_succ`](super::CRealPrelude::mono_of_le_succ) exactly
//! the way [`CReal.sumRange_mono_outer`](super::CRealPrelude::sum_range_mono_outer)
//! is, but with no nonnegativity hypothesis — `max`'s own step law
//! (`le_max_left`) needs none).
//!
//! **Also landed this session (route 2's first two rungs — see below):**
//! `CReal.meshLevelCount` (`Nat → Nat`, the geometric doubling schedule
//! `meshLevelCount j = 2^j − 1`, built additively so it needs no `Nat.mul`)
//! and `CReal.meshMax` (`(CReal → CReal) → CReal → CReal → Nat → CReal`, the
//! level-`j` mesh maximum `meshMax F a b j := maxRange (fun i => F(a +
//! i·Δⱼ)) (meshLevelCount j)`, `Δⱼ := (b−a)/(meshLevelCount j + 1)`). Both
//! are pure `Definition`s needing no hypothesis on `F`/`a`/`b` and no
//! continuity witness — the continuity only enters at the NEXT rung.
//!
//! **Also landed this session: `CReal.meshMax_step_le` and
//! `CReal.meshMax_mono`** (rungs 3 and 4 below), both first-attempt kernel
//! accepts. **Also landed, a later session: `CReal.expOfModulus` and
//! `CReal.trueExpOfModulus`** (rung 5, the accuracy-selection schedule)
//! plus `trueExpOfModulus`'s two defining equations,
//! `trueExpOfModulus_step_le`/`_mono` (adjacent-step and general
//! monotonicity, mirroring `meshMax_step_le`/`_mono` one type down), and
//! `expOfModulus_le_trueExpOfModulus` (the accumulator is always at least
//! as fine as the single level it covers) — five declarations, every one a
//! first-attempt kernel accept. Left generic over a modulus `m : Nat → Nat`
//! rather than tied to a specific `UniformlyContinuousOn` witness; callers
//! apply it at `m := UniformlyContinuousOn.modulus F a b u`. **Still not
//! landed: `CReal.supOn` itself**, and therefore none of deliverables
//! (a)/(b)/(c) the assignment names in fully assembled form. This is not a
//! hedge — it is the honest outcome of a real attempt at the full route,
//! and the remaining obstruction is now characterized much more precisely
//! than at the start of this session (below), which is the point of
//! recording it here rather than leaving a silent gap.
//!
//! ### Why `supOn` did not land, precisely — and the now-concrete plan for it
//!
//! `supOn` needs `CReal.mk (speedup f_lambda K) (regularity proof)`, built
//! **without** `Exists.rec` (kernel fact 1 — `K` and `f_lambda` must be
//! *concrete* data, never extracted from an existential, since they feed
//! `speedup`, a `Type`-level construction). Landing that regularity proof —
//! `∀ p q, Within (seq (f_lambda p) p − seq (f_lambda q) q) (natDivSucc K p +
//! natDivSucc K q)` — needs, for two *independent* accuracies `p`/`q`, a
//! bound relating a mesh maximum at one accuracy to one at another. That
//! bound needs, for an arbitrary point of one mesh, the *nearest point of the
//! other mesh* — a genuine "which cell" lookup, UNLESS the two meshes are
//! chosen to nest exactly, which is exactly what `meshLevelCount`'s doubling
//! schedule buys (below).
//!
//! Two routes were investigated and both are real, existing machinery — this
//! is not a case of the tool being missing, only of correctly assembling it
//! not fitting this session:
//!
//! 1. **Reuse `CReal.bucketIndex`/`bucketIndexFloorLower`/`bucketIndexFloorUpper`**
//!    (`creal/uniform_continuity.rs`, built for
//!    [`CReal.bounded_of_uniformly_continuous`](super::CRealPrelude::bounded_of_uniformly_continuous)'s
//!    own covering argument). These are public, already proved, and directly
//!    applicable in principle — but that covering argument is ~700 lines with
//!    real, documented subtleties (a `+2`/`+3` floor slack, a sign hypothesis
//!    on the lower clamp, a still-open gap the same file's `crossingClose`
//!    entry names explicitly). Reusing it correctly for a *different*
//!    quantity (a running maximum, not a single boundedness witness) is a
//!    genuine new proof, not a two-line application. **Rejected**, unchanged
//!    from the prior assessment.
//! 2. **A NESTED-REFINEMENT construction avoiding bucket-index entirely**
//!    (this file, in progress). `meshLevelCount`'s doubling means level `j`'s
//!    mesh points are EXACTLY a subset of level `j'`'s (`j' ≥ j`): a coarse
//!    sample `a + i·Δⱼ` equals the fine sample `a + (i·2^(j'−j))·Δⱼ'`, a pure
//!    index-scaling identity via
//!    [`Rat.natDivSucc_scale`](crate::RatPrelude::nat_div_succ_scale) /
//!    [`Rat.natDivSucc_mul`](crate::RatPrelude::nat_div_succ_mul) — no
//!    `Nat.div`, no search. That is the property route 1 does not have.
//!
//! **The remaining assembly, characterized precisely (verified against this
//! kernel's actual API this session, not just worked out on paper):**
//!
//! - **Rung 3, the order half — LANDED, and the plan below was subtly
//!   WRONG about its statement.** The actual, kernel-accepted signature is
//!   `meshMax_step_le : ∀ F a b j, UniformlyContinuousOn F a b → le a b → le
//!   (meshMax F a b j) (meshMax F a b (Nat.succ j))` — **not** hypothesis-free
//!   as first planned. `F` applied to the two `Equiv`-but-not-equal mesh
//!   points needs `F` to respect `Equiv`, which is exactly
//!   [`CRealPrelude::congr_of_uniformly_continuous`] and is FALSE for an
//!   arbitrary `F` with no continuity witness. This is NOT an instance of
//!   [`CReal.mono_of_le_succ`](super::CRealPrelude::mono_of_le_succ) the way
//!   `maxRange_mono` is (`mono_of_le_succ` holds the SAMPLING FUNCTION fixed
//!   and varies only `maxRange`'s own bound; here both the sampling function
//!   AND the bound change together as `j` grows). Built from
//!   [`CRealPrelude::max_range_transport`], induction on an AUXILIARY index
//!   `k` (motive `fun k => Nat.le k n → le (maxRange f k) (maxRange g n')`),
//!   base case via [`CRealPrelude::maxRange_ub`] plus
//!   [`CRealPrelude::le_congr`], step case via
//!   [`CRealPrelude::max_le`](super::CRealPrelude::max_le) combining the IH
//!   with a fresh `maxRange_ub` instance — see [`declare_max_range_transport_thm`]
//!   for that combinator's own construction. Instantiated at `e(i) := add i
//!   i` (built ADDITIVELY, matching `meshLevelCount`'s own convention — not
//!   `mul 2 i` as first planned, which would have needed a `Nat.mul`
//!   dependency this file otherwise avoids entirely), `n := meshLevelCount
//!   j`, `n' := meshLevelCount (succ j)` (`hbound` is pure `Nat` order
//!   algebra: `add_le_add_left`/`_right` plus `le_succ`, `le_trans`). The
//!   `Equiv` hypothesis places both sample points in `[a, b]` via
//!   [`CRealPrelude::riemann_sample_in_bounds`] (the same mesh-point shape
//!   `riemannSum` uses) and closes with
//!   [`CRealPrelude::congr_of_uniformly_continuous`] against
//!   [`mesh_sample_transport`]'s point-level `Equiv (meshSamplePoint a Δⱼ i)
//!   (meshSamplePoint a Δⱼ' (add i i))` — built from `ofNat (add i i) ~ add
//!   (ofNat i) (ofNat i)` ([`CRealPrelude::of_nat_add`], not `of_nat_mul` as
//!   first planned), [`right_distrib`]/[`CRealPrelude::left_distrib`], and
//!   [`mesh_delta_halve`]'s `Δⱼ' + Δⱼ' ~ Δⱼ` (via `Rat.natDivSucc_add` fusing
//!   the sum, then `Rat.natDivSucc_halve` rewritten along a small
//!   `mul 2 m = add m m` bridge lemma — not `natDivSucc_scale`/`_mul` as
//!   first planned, which multiply rather than add and so do not match
//!   `meshLevelCount`'s additive doubling directly).
//! - **Rung 4, general monotonicity — LANDED**, for free once rung 3 lands:
//!   `meshMax_mono : ∀ F a b, UniformlyContinuousOn F a b → le a b → ∀ j j',
//!   Nat.le j j' → le (meshMax F a b j) (meshMax F a b j')` (`F`/`a`/`b`/the
//!   continuity witness/`le a b` closed over rather than varying, since
//!   rung 3's hypotheses are needed at every adjacent step), by
//!   [`CRealPrelude::mono_of_le_succ`] applied to `fun j => meshMax F a b j`
//!   with rung 3 as the adjacent step — EXACTLY
//!   [`declare_max_range_mono`]'s own construction, one level up.
//! - **Rung 5, the accuracy-selection scheme (where continuity enters).**
//!   The naive choice — request the SAME accuracy `k` as the outer `CReal`
//!   index — fails: uniform continuity at request `k` only bounds the
//!   one-step gap by `1/(k+1)` (the HARMONIC series, not summable), so the
//!   telescoped tail never converges. The level-`k` mesh must instead be fine
//!   enough for accuracy request `2^k − 1` (i.e. `meshLevelCount k` itself,
//!   reusing that same function as the REQUESTED accuracy index), giving a
//!   one-step gap `≤ 1/2^k` — summable — via
//!   `Nat.lt_pow_size : ∀ n, Lt n (pow 2 (size n))` (confirmed to exist,
//!   `nat_prelude.rs`) to turn `u.modulus(meshLevelCount k)`, an ARBITRARY
//!   `Nat`, into a POWER-OF-TWO exponent comfortably above it, with NO
//!   `Nat.div`/search: `exponent(k) := Nat.size (u.modulus (meshLevelCount
//!   k))`. `exponent` need not be monotone (an arbitrary modulus need not
//!   be), so nesting needs a running accumulator forcing monotonicity —
//!   **use `Nat.add`, not `Nat.max`: this kernel's `Nat` prelude has no
//!   `Nat.max`,** and addition suffices (`trueExponent 0 := exponent 0`,
//!   `trueExponent (succ k) := add (trueExponent k) (exponent (succ k))`,
//!   monotone via [`Nat.le_add_right`](crate::NatPrelude::le_add_right) and
//!   `≥ exponent(k)` via the same lemma read through `Nat.add_comm`). The
//!   final `f_lambda(k) := meshMax F a b (trueExponent k)` is then genuinely
//!   nested (rung 3/4 apply, `j := trueExponent k`), and the per-level
//!   gap is bounded by `1/2^k` via the modulus applied at accuracy request
//!   `meshLevelCount k` on the KNOWN, closed-form displacement between a
//!   fine point and its immediate coarse neighbour (no bucket search — the
//!   doubling nesting makes that displacement exact, not merely bounded).
//!   **This "immediate coarse neighbour" framing is only exact for a
//!   SINGLE doubling (`j → j+1`); `trueExponent(k) → trueExponent(k+1)` is
//!   not, in general, one doubling — see the "Rung 6 re-verified" section
//!   below, which corrects this.**
//! - **Rung 6, the telescope (ORIGINAL sketch — see the correction below
//!   before acting on this).** Sum the per-level gaps via
//!   [`CReal.sumRange_cauchy_of_dominated`](super::CRealPrelude::sum_range_cauchy_of_dominated)
//!   (`creal/series.rs`) against a CONCRETE ratio-`1/2` geometric dominator —
//!   **`creal/geometric.rs` already proves `Cauchy (sumRange (fun n => pow x
//!   n))` for `x` bounded away from `1` by a witnessed `PosBound`**
//!   (`geom_tail_bounded_div`/`geom_tail_within`, that file's own module
//!   documentation), and at the CONCRETE `x := natDivSucc 1 1` (`= 1/2`) the
//!   needed `PosBound (add one (neg x)) k` witness is immediate (no
//!   apartness search — `1 − 1/2 = 1/2` is a fixed rational, not an arbitrary
//!   hypothesis). A constant-multiple corollary (scaling a Cauchy bound by a
//!   fixed positive `CReal` constant) is the one piece here NOT already
//!   confirmed to exist by name and may need a short derivation.
//! - **Rung 7.** Feed the resulting `K`-scaled Cauchy witness to
//!   [`CReal.regular_of_scaled_cauchy`](super::CRealPrelude::regular_of_scaled_cauchy),
//!   exactly [`declare_creal_integral`](super::integral::declare_creal_integral)'s
//!   own `CReal.mk (speedup f_lambda K) (regular_of_scaled_cauchy f_lambda K
//!   h)` shape (kernel fact 1 respected: `f_lambda`/`K` stay concrete data
//!   throughout, never pulled from an `Exists`).
//!
//! ### Rung 6 re-verified against the kernel API (2026-08-27) — the sketch
//! above UNDERSOLD what remains, and this is a correction, not a restatement
//!
//! The "constant-multiple corollary" the rungs-1–5 sketch names as the one
//! open piece is **not** the bottleneck — it already exists in substance.
//! [`geometric.rs::declare_geom_cauchy`]'s own construction (and
//! `exponential.rs::exp_dominant_cauchy_body_concrete`/
//! `trig.rs`'s `pub(super)` copies `mul_ordered_half_body` +
//! `promote_ordered_half_to_full` + `telescope_cauchy_pad2`) already scale a
//! ratio-`1/2` ordered-half Cauchy bound by a fixed positive `CReal`
//! constant and promote it past `Nat.le_total` — reusable machinery, not
//! missing machinery. Likewise
//! [`CReal.cauchy_of_abs_diff_le`](super::CRealPrelude::cauchy_of_abs_diff_le)
//! (`creal/ivt.rs`) is the exact general REAL-valued-bound-to-canonical-
//! sample bridge a telescoped estimate needs, and its own body (before the
//! final `cexists_intro`) already produces the RAW `(K, per-pair proof)`
//! pair [`CReal.regular_of_scaled_cauchy`](super::CRealPrelude::regular_of_scaled_cauchy)
//! needs as DATA (kernel fact 2) — reproducible here the way this
//! development always reproduces a sibling's private helper rather than
//! widening its visibility for one caller.
//!
//! **What actually blocks rung 6 is the per-level GAP BOUND itself — a real
//! quantitative estimate this file has never built, not yet even attempted
//! against the kernel — and it is harder than "sum the gaps" suggests,
//! because `f_lambda`'s consecutive terms are NOT adjacent mesh levels.**
//! `f_lambda(k) := meshMax F a b (trueExpOfModulus m k)`, and
//! `trueExpOfModulus`'s own defining recursion
//! (`trueExpOfModulus m (succ k) := add (trueExpOfModulus m k) (expOfModulus
//! m (succ k))`) can jump the mesh level by an ARBITRARILY large number of
//! doublings between `f_lambda(k)` and `f_lambda(k+1)` — `expOfModulus m
//! (succ k) := Nat.size (m (meshLevelCount (succ k)))` depends on the
//! continuity modulus `m`, which this file is generic over and which can
//! grow arbitrarily fast. So the needed bound is not "adjacent mesh levels
//! differ by `≤ 1/2^k`" (a single doubling, which [`mesh_sample_transport`]
//! and [`mesh_delta_halve`] do make cheap via the EVEN-index exact
//! coincidence) — it is "level `trueExpOfModulus(k)` and level
//! `trueExpOfModulus(k+1)` differ by `≤ 1/2^k`, however many doublings apart
//! they are," and EVERY fine-level sample point that is not an exact
//! even-index descendant of a coarse point needs to be related to SOME
//! nearby coarse point — a genuine index/"nearest point" fact, at ANY
//! refinement depth, not just depth 1.
//!
//! That is precisely the shape of problem [`creal/uniform_continuity.rs`]'s
//! `bucketIndex`/`crossingClose`/`crossingSampleUpper`/`crossingSampleLower`
//! family exists to solve (this file's own §"Why supOn did not land"
//! already names this as "route 1", rejected as too costly to adapt) — and
//! re-reading that family's OWN field documentation this session
//! (`CReal.crossing_close`, `creal.rs`) shows it is not a free reuse even on
//! its own terms: `crossingClose`'s domain-membership side condition
//! (`samplePt ≤ b`) is recorded there as **still open**, independently
//! discovered and refuted-by-worked-example across five of `integral.rs`'s
//! own 2026-08-27 module-doc entries. Reusing route 1 here would import an
//! open gap, not a finished lemma.
//!
//! So route 2, as characterized above, does **not** actually avoid an
//! index/bucket-style argument for the full construction — it only avoids
//! one for a SINGLE adjacent doubling. Two ways forward, neither attempted
//! this session, both larger than "a short derivation":
//!
//! 1. **Bound the whole multi-level jump with ONE continuity application at
//!    the COARSE level**, using that binary-doubling refinement never
//!    leaves its parent cell: every point sampled at ANY level `j' ≥ j`
//!    lies within one full coarse cell width `Δⱼ` of that cell's LEFT
//!    endpoint (no "nearest" comparison needed — always the left one), so
//!    ONE application of [`CRealPrelude::uc_spec`] at accuracy request
//!    tied to `meshLevelCount k` bounds the ENTIRE jump regardless of how
//!    many doublings `expOfModulus m (succ k)` represents. This still needs
//!    a genuine (if bounded) index computation — "which coarse cell
//!    contains fine index `i'`" — that [`mesh_sample_transport`]'s exact
//!    doubling identity does not supply once more than one doubling is
//!    involved.
//! 2. **A double telescope**: bound each SINGLE adjacent-level step (the
//!    one case this file's existing machinery already makes cheap) by a
//!    per-step accuracy that itself decreases geometrically across the
//!    (unboundedly many) intermediate levels within one `k`-to-`k+1` block,
//!    then sum that inner geometric series (bounded by twice its first
//!    term, [`geom_tail_within`]-style) to get the block bound, then sum
//!    the outer series across `k` as originally planned. This needs an
//!    intermediate accuracy SCHEDULE finer-grained than `expOfModulus`
//!    supplies today (one number per outer `k`, not per intermediate mesh
//!    level within a block).
//!
//! Neither is "a short derivation." Both are comparable in scope to a
//! rung of their own. This correction does not change the earlier,
//! carefully-hedged claim about the ACCURACY SCHEDULE itself: `expOfModulus`
//! at `meshLevelCount k` genuinely does fix the naive harmonic-series trap
//! **in the sense that the requested accuracy is summable** (`1/2^k`, via
//! [`declare_exp_of_modulus_le_true_exp_of_modulus_thm`] plus
//! `Nat.lt_pow_size`) — what is still unverified against the kernel is
//! whether that requested accuracy is actually ACHIEVED by
//! `meshMax`'s value at the corresponding level, which is exactly the gap
//! bound above.
//!
//! ### Rung 6 LANDED (2026-08-28) -- and the section above was right about
//! WHAT blocks it and wrong about WHY it is expensive
//!
//! Three declarations, each a first-attempt kernel accept:
//!
//! - [`CRealPrelude::mesh_point_near_coarse`] -- the MULTI-LEVEL
//!   nearest-mesh-point lemma. `forall a b j, le a b -> forall d i',
//!   Nat.le i' (meshLevelCount (add j d)) -> exists i, Nat.le i
//!   (meshLevelCount j) /\ le (P j i) (P (add j d) i') /\ le (add (P (add j
//!   d) i') (D (add j d))) (add (P j i) (D j))`, writing `P L i` for the
//!   level-`L` sample point and `D L` for the level-`L` width.
//! - [`CRealPrelude::max_range_le_add_of_exists`] -- the approximate,
//!   existential-witnessed form of [`CRealPrelude::max_range_transport`].
//! - [`CRealPrelude::mesh_max_le_add_of_step_close`] -- the GAP BOUND:
//!   `le (meshMax F a b (add j d)) (add (meshMax F a b j) eps)`, at arbitrary
//!   depth `d`, from a one-sided pointwise hypothesis on `F`.
//!
//! **The diagnosis above is correct and the cost estimate is not.** The
//! section is right that the blocker is the per-level gap bound, right that
//! `trueExpOfModulus` can jump the mesh level by arbitrarily many doublings,
//! and right that a "nearest coarse point at ANY refinement depth" fact is
//! what that needs. Its two candidate routes are both real. But it calls each
//! "comparable in scope to a rung of their own" because it assumes the coarse
//! index has to be COMPUTED -- route 1 "still needs a genuine (if bounded)
//! index computation", route 2 needs a finer accuracy schedule.
//!
//! **It does not. The gap bound's conclusion is `Prop`, so the coarse index
//! can be an `Exists` witness that the induction step re-eliminates.** Kernel
//! fact 2 (`Exists.rec` is `Prop`-only) is a constraint on rung 7's
//! `CReal.mk`, where `K` and `f_lambda` are DATA; it says nothing about a
//! `le`-valued estimate. Once the index is existential, "which coarse cell
//! contains fine index `i'`" never has to be answered: induct on the depth
//! `d` and split the fine index's parity with
//! [`NatPrelude::even_or_odd`](crate::NatPrelude::even_or_odd), whose half is
//! the COMPUTED `Nat.div i' 2` used only inside a `Prop`. No quotient/
//! remainder algebra, no `bucketIndex`, no schedule refinement, and
//! `uniform_continuity.rs`'s still-open `crossingClose` side condition is
//! never touched -- so nothing here imports that gap. What made
//! [`CRealPrelude::max_range_transport`] look like it forced a function
//! `e : Nat -> Nat` is simply that it was stated with one;
//! [`CRealPrelude::max_range_le_add_of_exists`] is the same induction
//! restated to take a witness instead.
//!
//! **The one thing that genuinely does not work, and it is a statement
//! choice, not a technique.** The obvious invariant -- "every fine point is
//! within one coarse width of some coarse point",
//! `le (P L i') (add (P j i) (D j))` -- does NOT close the induction. Each
//! odd step adds a fine width, and the accumulated displacement across
//! unboundedly many doublings is only bounded because the widths halve, which
//! that statement cannot see. Carrying the FINE width on the left instead --
//! `le (add (P L i') (D L)) (add (P j i) (D j))` -- makes every step EXACT:
//! the even step is [`mesh_sample_transport`]'s coincidence plus
//! `D (succ L) <= D L`, and the odd step's two fine widths fuse back to one
//! coarse width by [`mesh_delta_halve`], with equality rather than an
//! estimate. That is the whole difficulty of the lemma, and it is visible
//! only in the statement.
//!
//! **What rung 6 still owes, precisely.** `mesh_max_le_add_of_step_close`
//! takes `hclose` as a hypothesis: `forall x y, x,y in [a, b] -> le x y ->
//! le y (add x (D j)) -> le (F y) (add (F x) eps)`. Instantiating it from
//! [`CRealPrelude::uc_spec`] at the accuracy [`CRealPrelude::exp_of_modulus`]
//! selects is arithmetic about the modulus with NO mesh geometry left in it:
//! it needs `D j` (an arbitrary `CReal` interval width divided by `2^j`)
//! compared against `1/(m k + 1)`, which is where `Nat.lt_pow_size` and an
//! Archimedean bound on `b - a` enter. Rungs 6b and 7 (the telescope and
//! `regular_of_scaled_cauchy`) are unchanged by any of this; the
//! constant-multiple corollary and `cauchy_of_abs_diff_le` claims above were
//! NOT exercised by this work and remain as that section left them.
//!
//! This plan was grounded against the kernel's actual API, and rungs 1–5
//! have now all built cleanly on the first attempt by mirroring
//! `declare_max_range`'s and `integral.rs`'s existing shapes exactly rather
//! than composing primitives from scratch — the same held for rung 3's own
//! sub-lemmas ([`mesh_delta_halve`], [`mesh_sample_transport`]), each of
//! which needed one correction against the ORIGINAL plan above (documented
//! inline at rung 3: additive doubling and `natDivSucc_add`/`_halve` in
//! place of the originally planned multiplicative route, and an added
//! `UniformlyContinuousOn`/`le a b` hypothesis the original statement
//! omitted). **Rung 5 landed exactly as planned above** — `expOfModulus`
//! and `trueExpOfModulus`, no correction needed against the original
//! sketch — but the harmonic-vs.-summable trap the rung exists to fix is
//! still UNVERIFIED against the kernel in the sense that matters: rung 5
//! builds the schedule and its two structural facts (monotone, `≥` the
//! single level requested), not the per-level gap bound itself, so nothing
//! has yet forced the kernel to check that requesting `meshLevelCount k`
//! rather than `k` actually produces a summable tail. **The next concrete
//! task is the per-level GAP BOUND itself** (the "Rung 6 re-verified"
//! section above, added this session, supersedes this paragraph's earlier
//! framing of rung 6 as "sum the gaps" — the summing machinery is ready and
//! waiting; the gap bound it would sum is not built yet, and is the actual
//! remaining mathematics). Not attempted against the kernel this session —
//! see that section for the two candidate routes and why neither is small.
//!
//! ### `CReal.supOn` LANDED (2026-08-30). Everything above is history; read
//! this section first.
//!
//! `CReal.supOn : ∀ F a b, le a b → UniformlyContinuousOn F a b → CReal` is
//! in the prelude, derived and axiom-free, together with
//! `CReal.supSeq_converges_supOn` tying it to the sequence it is built from.
//! Thirteen declarations closed the gap, in four rungs; twelve were
//! first-attempt kernel accepts and the thirteenth failed once on a
//! `pi_fv`/`arrow` binder.
//!
//! **What the plan above got right.** Route 2 (nested refinement) was the
//! right route and route 1 (`bucketIndex`) was correctly rejected —
//! `uniform_continuity.rs`'s open `crossingClose` side condition is never
//! touched by anything here. Rung 5's accuracy schedule composed EXACTLY as
//! designed: `expOfModulus m k` is literally `Nat.size (m (meshLevelCount k))`,
//! which is definitionally the `Nat.size (modulus n)` at `n := meshLevelCount
//! k` that the width bound needs, so `expOfModulus_le_trueExpOfModulus` slots
//! in under one `Nat.add_le_add_left` with nothing recomputed. The
//! "Rung 6 re-verified" section's diagnosis — that the blocker was the
//! per-level gap bound and that it needed a nearest-coarse-point fact at
//! ARBITRARY depth — was correct, and its own correction (make the coarse
//! index an `Exists` witness, since the conclusion is `Prop`) is what made the
//! rest cheap.
//!
//! **Three things the plan got wrong, all in the same direction: it
//! oversized what remained.**
//!
//! 1. **No telescope is needed, and neither is the double telescope.** The
//!    plan sizes rung 6b as "sum the per-level gaps", and worries that
//!    `trueExpOfModulus` can jump the mesh level by arbitrarily many
//!    doublings within one `k`-to-`k+1` block, so that an inner geometric
//!    series across intermediate levels might be required. It is not.
//!    [`CRealPrelude::mesh_max_le_add_of_step_close`] is already
//!    DEPTH-UNIFORM — it takes an arbitrary depth `d` and uses the same
//!    epsilon at every depth — so the estimate at `k' ≥ k` is ONE
//!    application, and how many doublings separate them never enters.
//!    `Nat.le_dest` supplies the `add j d` shape. The double telescope would
//!    have been machinery for a difficulty the previous rung had already
//!    removed.
//! 2. **The schedule was missing the interval WIDTH, and nothing above says
//!    so.** `expOfModulus` schedules only the modulus. The mesh width is
//!    `(b − a)/2^j`, so the level must also absorb `b − a`; without that the
//!    construction is correct only on intervals of width at most one.
//!    [`CRealPrelude::sup_level`] is `Nat.size (CReal.bound (b − a)) +
//!    trueExpOfModulus m k` — one summand per factor of
//!    [`CRealPrelude::mesh_le_of_ge`]'s threshold. The width term is constant
//!    in `k`, so monotonicity is undisturbed.
//! 3. **`CReal.mesh_le_of_ge` already existed and is exactly the Archimedean
//!    rescaling this file needed.** It is in `creal/integral.rs`, filed under
//!    the consumer that first needed it, and its left-hand side is
//!    SYNTACTICALLY this file's own `mesh_delta a b m`. It reads its
//!    threshold off `CReal.bound`, a total computable projection — never off
//!    `CReal.archimedean`'s `Exists` — which is what keeps the whole route
//!    clear of kernel fact 1. This is hiding place 1 from CLAUDE.md's
//!    retrieval section, exactly: general infrastructure filed under its first
//!    consumer's module. `examples/shape_search` found it in one query.
//!
//! **The rungs, as landed.**
//!
//! - **6c** [`CRealPrelude::mesh_level_count_ge_of_size`]. At which mesh LEVEL
//!   does the doubling schedule reach `mesh_le_of_ge`'s threshold? Via
//!   `meshLevelCount_pow` the question is `2^j ≥ (c+1)·(outer+1)`, and
//!   `Nat.lt_pow_size` answers it one factor at a time, with `Nat.pow_add`
//!   turning a SUM in the exponent into the PRODUCT of the two bounds — so the
//!   schedule stays additive. The last step is two `Eq.refl`s, and they are
//!   refl only because `Nat.mul` and `Nat.add` both recurse on their RIGHT
//!   argument.
//! - **6d** [`CRealPrelude::mesh_max_le_add_of_modulus`]. `hclose` instantiated
//!   from `uc_spec` — the one obligation `mesh_max_le_add_of_step_close`'s own
//!   documentation said a `supOn` assembly still owed. No mesh geometry
//!   survives into the hypothesis; it is a `Nat` bit-count inequality. Note
//!   `uc_spec` is applied at SWAPPED arguments, since its conclusion puts the
//!   first argument on the left of `|F x − F y|` and `hclose` wants `F y`
//!   there.
//! - **6e** [`CRealPrelude::sup_level`], [`CRealPrelude::sup_seq`] and their
//!   order facts, including [`CRealPrelude::sup_seq_le_add`] — the whole of
//!   point 1 above.
//! - **6f** [`CRealPrelude::sup_seq_cauchy`], at `K = 1`. `K = 1` is what the
//!   geometric schedule buys, not a tuning choice.
//! - **7** [`CRealPrelude::sup_on`] and
//!   [`CRealPrelude::sup_seq_converges_sup_on`].
//!
//! **Note the two readings of the rate, which coexist only because rung 6 is
//! depth-uniform.** The schedule REQUESTS the summable `1/2^k` — requesting
//! `1/(k+1)` directly is the harmonic trap rung 5 exists to avoid — and then
//! WEAKENS it to `1/(k+1)` for the Cauchy modulus, where `1/(k+1)` is fine
//! precisely because nothing is being summed.
//!
//! **One refactor outside this file.** `cauchy_of_abs_diff_le` built the raw
//! `(K+2, per-pair)` pair and immediately closed an `Exists` over it. That
//! pair is what `regular_of_scaled_cauchy` needs as DATA, and kernel fact 2
//! means `Cauchy f` can never give it back, so the declaration was split at
//! that point into [`CRealPrelude::scaled_cauchy_of_abs_diff_le`] plus a
//! one-line `cexists_intro`. No proof content moved. The "Rung 6 re-verified"
//! section anticipated needing this body and suggested reproducing it here;
//! extracting is better, because two copies of one 300-line seven-term bound
//! would have to stay in sync while the kernel verifies both.
//!
//! ### What `supOn` does NOT yet give, stated precisely
//!
//! `supOn` is a VALUE with a `Converges` law, and that is all. It is not yet
//! characterized as a supremum. Two declarations are missing, and they are
//! the difference between "a real exists" and "EVT":
//!
//! - **The upper-bound law**, `∀ x, le a x → le x b → le (F x) (supOn F a b
//!   hab u)`. An arbitrary `x` is not a mesh point, so this needs `x` placed
//!   within one cell of some mesh point (available: the same
//!   `riemann_sample_in_bounds`/`uc_spec` pairing rung 6d already uses), then
//!   [`CRealPrelude::max_range_ub`] at that index, then a limit passage
//!   through `supSeq_converges_supOn`. The mesh index for `x` is where a
//!   `bucketIndex`-style lookup DOES seem to be needed — but the conclusion is
//!   `Prop`, so rung 6's own trick (make the index an `Exists` witness)
//!   should apply again, and `meshPoint_near_coarse` is the wrong shape only
//!   because it relates two MESHES rather than a point to a mesh.
//! - **The least-upper-bound law**, in its constructive form: for every
//!   `eps > 0` there is a point of `[a, b]` at which `F` exceeds `supOn −
//!   eps`. Note this is an APPROXIMATE statement and must stay one —
//!   [`super::ExtremeValueNames::evt_attained_max_decides_sign`] rules out the
//!   exact version, which is precisely why EVT's row 2 exists.
//!
//! Until the upper-bound law lands, `supOn` is honestly described as "the
//! limit of the mesh maxima, which is the supremum", with the second clause
//! not yet machine-checked.

#![allow(clippy::doc_markdown, clippy::too_many_arguments)]

use super::ring_helpers::right_distrib;
use super::{CRealPrelude, and_intro, cadd, cle, creal_ty, embed};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{nat_rewrite_prop, radd, rat_eq_rewrite, req, rle, rtrans, rzero};

/// Reducibility height for [`declare_max_range`]'s `Definition`. Deliberately
/// far above [`super::DERIVED_HEIGHT`] plus every other derived-operation
/// offset in this file's build neighbourhood — `maxRange` depends only on
/// `CReal.max` (declared in `creal/lattice.rs`, itself near the bottom of the
/// height order), so any height comfortably above the existing offsets used
/// elsewhere in `creal.rs` is safe; the exact number carries no meaning
/// beyond "unfolds no more eagerly than it has to".
const MAX_RANGE_HEIGHT: u16 = super::DERIVED_HEIGHT + 500;

/// `Eq.{1} CReal a b` — mirrors `series.rs`'s private `creal_eq` (not
/// `pub(super)`, so re-derived here from the same public primitives rather
/// than imported).
fn creal_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let eq = d.kernel().const_(logic.eq, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(eq, &[carrier, a, b])
}

/// `Eq.refl.{1} CReal a` — mirrors `series.rs`'s private `creal_eq_refl`.
fn creal_eq_refl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let refl = d.kernel().const_(logic.eq_refl, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(refl, &[carrier, a])
}

/// `CReal.maxRange : (Nat → CReal) → Nat → CReal`, structural `Nat.rec` on
/// the bound: `maxRange f 0 := f 0`, `maxRange f (succ n) := max (maxRange f
/// n) (f (succ n))` — so `maxRange f n` is `max_{k≤n} f k` (`n+1` sampled
/// points, unlike `CReal.sumRange`'s `k<n`/`n` points convention: a maximum
/// needs a real starting VALUE, not an identity element, so it anchors at
/// `f 0` rather than at a `zero` the way `sumRange` does).
fn declare_max_range_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d
        .kernel()
        .lam(anon, nat, carrier, crate::BinderInfo::Default);
    let zero_n = d.zero();
    let minor_zero = d.apply(f, &[zero_n]);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let sj = d.succ(j);
        let fsj = d.apply(f, &[sj]);
        let body = d.const_app(p.max, &[ih, fsj]);
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
        name: p.max_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// `CReal.maxRange_zero`/`CReal.maxRange_succ`: the defining equations of
/// [`declare_max_range`], each closed by `Eq.refl` alone since `maxRange`'s
/// `Nat.rec` application ι-reduces on both minor premises (mirrors
/// `series.rs`'s `declare_sum_range_equations`).
fn declare_max_range_equations(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let _ = carrier;

    // maxRange_zero : ∀ f, Eq CReal (maxRange f Nat.zero) (f Nat.zero).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero_n = d.zero();
        let lhs = d.const_app(p.max_range, &[f, zero_n]);
        let f0 = d.apply(f, &[zero_n]);
        let stmt = creal_eq(d, p, lhs, f0);
        let proof = creal_eq_refl(d, p, f0);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.max_range_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // maxRange_succ : ∀ f (n : Nat),
    //   Eq CReal (maxRange f (succ n)) (max (maxRange f n) (f n... succ n)).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = d.const_app(p.max_range, &[f, sn]);
        let prior = d.const_app(p.max_range, &[f, n]);
        let fsn = d.apply(f, &[sn]);
        let rhs = d.const_app(p.max, &[prior, fsn]);
        let stmt_inner = creal_eq(d, p, lhs, rhs);
        let proof_inner = creal_eq_refl(d, p, rhs);
        let ty = {
            let inner = d.pi_fv(n_fv, nat, stmt_inner);
            d.pi_fv(f_fv, fn_ty, inner)
        };
        let value = {
            let inner = d.lam_fv(n_fv, nat, proof_inner);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.max_range_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `CReal.maxRange_self_le : ∀ f n, le (f n) (maxRange f n)` — every sampled
/// value is at most the running maximum through its own index. `Nat.rec`
/// case analysis (no inductive hypothesis is used): the base case is
/// `le_refl` against `maxRange f 0`'s ι-reduction to `f 0`, the successor
/// case is `le_max_right` against `maxRange f (succ j)`'s ι-reduction to
/// `max (maxRange f j) (f (succ j))` — both close by defeq alone, the same
/// way `maxRange_zero`/`maxRange_succ` do.
fn declare_max_range_self_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let _ = carrier;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let fx = d.apply(f, &[x]);
        let mr = d.const_app(p.max_range, &[f, x]);
        cle(d, p, fx, mr)
    };

    let proof = d.induct(
        &motive,
        &|d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            let f0 = d.apply(f, &[zero_n]);
            d.lemma(p.le_refl, &[f0])
        },
        &|d: &mut IntDev<'_>, j: ExprId, _ih: ExprId| -> ExprId {
            let sj = d.succ(j);
            let mr_j = d.const_app(p.max_range, &[f, j]);
            let fsj = d.apply(f, &[sj]);
            d.lemma(p.le_max_right, &[mr_j, fsj])
        },
        n,
    );

    let stmt = motive(d, n);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_range_self_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.maxRange_mono : ∀ f m n, Nat.le m n → le (maxRange f m) (maxRange f
/// n)` — monotonicity of the running maximum in its own bound. Built from
/// [`CRealPrelude::mono_of_le_succ`] applied to `fun k => maxRange f k`,
/// exactly the way
/// [`declare_sum_range_mono_outer`](super::series) builds
/// [`CRealPrelude::sum_range_mono_outer`] — but with **no** nonnegativity
/// hypothesis: the adjacent step `le (maxRange f n) (maxRange f (succ n))`
/// is `le_max_left` applied at `(maxRange f n, f (succ n))` directly (defeq
/// to `maxRange f (succ n)`'s own ι-reduction), unlike `sumRange`'s adjacent
/// step, which genuinely needs `f n ≥ 0` to shift by a nonnegative summand.
fn declare_max_range_mono(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let _ = carrier;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let max_f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.max_range, &[f, k]);
        d.lam_fv(k_fv, nat, body)
    };

    let adjacent = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let mr_n = d.const_app(p.max_range, &[f, n]);
        let sn = d.succ(n);
        let fsn = d.apply(f, &[sn]);
        let body = d.lemma(p.le_max_left, &[mr_n, fsn]);
        d.lam_fv(n_fv, nat, body)
    };

    let mono = d.const_app(p.mono_of_le_succ, &[max_f, adjacent]);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hmn_fv = d.fresh_fvar();
    let hmn = d.kernel().fvar(hmn_fv);
    let hmn_ty = d.le(m, n);
    let applied = d.apply(mono, &[m, n, hmn]);

    let mr_m = d.const_app(p.max_range, &[f, m]);
    let mr_n = d.const_app(p.max_range, &[f, n]);
    let conclusion = cle(d, p, mr_m, mr_n);

    let ty = {
        let anon = d.anon_name();
        let out = d
            .kernel()
            .pi(anon, hmn_ty, conclusion, crate::BinderInfo::Default);
        let out = d.pi_fv(n_fv, nat, out);
        let out = d.pi_fv(m_fv, nat, out);
        d.pi_fv(f_fv, fn_ty, out)
    };
    let value = {
        let out = d.lam_fv(hmn_fv, hmn_ty, applied);
        let out = d.lam_fv(n_fv, nat, out);
        let out = d.lam_fv(m_fv, nat, out);
        d.lam_fv(f_fv, fn_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_range_mono,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.maxRange_ub : ∀ f n i, Nat.le i n → le (f i) (maxRange f n)` — the
/// upper-bound property every consumer of a finite maximum actually wants:
/// **any** sampled value up to and including the bound, not only the last
/// one. [`CRealPrelude::max_range_self_le`] at `i` (`le (f i) (maxRange f
/// i)`) composed with [`CRealPrelude::max_range_mono`] at `(i, n, hin)` (`le
/// (maxRange f i) (maxRange f n)`) via [`CRealPrelude::le_trans`] — no new
/// induction needed, since both ingredients already are one.
fn declare_max_range_ub(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let _ = carrier;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hin_fv = d.fresh_fvar();
    let hin = d.kernel().fvar(hin_fv);
    let hin_ty = d.le(i, n);

    let self_le = d.lemma(p.max_range_self_le, &[f, i]);
    let mono = d.lemma(p.max_range_mono, &[f, i, n, hin]);
    let fi = d.apply(f, &[i]);
    let mr_i = d.const_app(p.max_range, &[f, i]);
    let mr_n = d.const_app(p.max_range, &[f, n]);
    let proof = d.lemma(p.le_trans, &[fi, mr_i, mr_n, self_le, mono]);

    let conclusion = cle(d, p, fi, mr_n);
    let ty = {
        let anon = d.anon_name();
        let out = d
            .kernel()
            .pi(anon, hin_ty, conclusion, crate::BinderInfo::Default);
        let out = d.pi_fv(i_fv, nat, out);
        let out = d.pi_fv(n_fv, nat, out);
        d.pi_fv(f_fv, fn_ty, out)
    };
    let value = {
        let out = d.lam_fv(hin_fv, hin_ty, proof);
        let out = d.lam_fv(i_fv, nat, out);
        let out = d.lam_fv(n_fv, nat, out);
        d.lam_fv(f_fv, fn_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_range_ub,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.maxRange` and its order theory: the `Definition`, its two
/// defining equations, and the two order facts (`maxRange_self_le`,
/// `maxRange_mono`, composed into `maxRange_ub`) documented above.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_max_range(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_max_range_def(d, p)?;
    declare_max_range_equations(d, p)?;
    declare_max_range_self_le(d, p)?;
    declare_max_range_mono(d, p)?;
    declare_max_range_ub(d, p)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `CReal.maxRange_transport` -- rung 3's general combinator: comparing two
// DIFFERENT `maxRange` folds (different sampling function, different bound)
// related by an index embedding. See this module's own documentation,
// "Rung 3, the order half", for why this is NOT an instance of
// `mono_of_le_succ` and for the induction this builds.
// ---------------------------------------------------------------------------

/// `CReal.equiv x y` — mirrors the file's own `cle`/`cadd`/`embed` helpers
/// (imported from `super`), re-derived here since none of the sibling files
/// exports an `Equiv`-application helper under a name this file can import.
fn cequiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.equiv, &[x, y])
}

/// `CReal.maxRange_transport : ∀ f g n n' e, (∀ i, Nat.le i n → Nat.le (e i)
/// n') → (∀ i, Nat.le i n → Equiv (f i) (g (e i))) → le (maxRange f n)
/// (maxRange g n')`.
///
/// Proved by induction on an AUXILIARY index `k`, motive `fun k => Nat.le k
/// n → le (maxRange f k) (maxRange g n')`, instantiated at `k := n` (target
/// of the [`NatOps::induct`] call) and discharged with `Nat.le_refl n` —
/// **not** induction on `n` itself, since `n` is a parameter shared by every
/// case, not the thing being inducted on.
///
/// - **Base** (`k = 0`, hypothesis `h0 : Nat.le 0 n`): `maxRange_ub g n' (e
///   0) (hbound 0 h0)` gives `le (g (e 0)) (maxRange g n')`; `le_congr`
///   transports it across `equiv_symm (heq 0 h0) : Equiv (g (e 0)) (f 0)`
///   (the pre-substitution type is `le (g (e 0)) (maxRange g n')`, matching
///   `le_congr`'s own convention) to `le (f 0) (maxRange g n')` — defeq to
///   the goal since `maxRange f 0 ≡ f 0` by ι-reduction, exactly the defeq
///   [`declare_max_range_self_le`]'s own base case leans on.
/// - **Step** (`k = succ j`, hypothesis `hsj : Nat.le (succ j) n`, `ih : Nat.le
///   j n → le (maxRange f j) (maxRange g n')`): `hj := le_trans (le_succ j)
///   hsj : Nat.le j n` feeds `ih hj`; a second `maxRange_ub`/`le_congr`
///   instance at `succ j` (identical shape to the base case) gives `le (f
///   (succ j)) (maxRange g n')`; [`CRealPrelude::max_le`] combines the two
///   into `le (max (maxRange f j) (f (succ j))) (maxRange g n')`, defeq to
///   the goal since `maxRange f (succ j) ≡ max (maxRange f j) (f (succ
///   j))`, exactly the defeq [`declare_max_range_mono`]'s own step leans on.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_max_range_transport_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let np_fv = d.fresh_fvar();
    let np = d.kernel().fvar(np_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let hbound_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.le(i, n);
        let ei = d.apply(e, &[i]);
        let concl = d.le(ei, np);
        let inner = d.arrow(hi_ty, concl);
        d.pi_fv(i_fv, nat, inner)
    };
    let hbound_fv = d.fresh_fvar();
    let hbound = d.kernel().fvar(hbound_fv);

    let heq_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.le(i, n);
        let fi = d.apply(f, &[i]);
        let ei = d.apply(e, &[i]);
        let gei = d.apply(g, &[ei]);
        let equiv_i = cequiv(d, p, fi, gei);
        let inner = d.arrow(hi_ty, equiv_i);
        d.pi_fv(i_fv, nat, inner)
    };
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    // Auxiliary induction motive: `fun k => Nat.le k n -> le (maxRange f k)
    // (maxRange g n')`. `h` (the `Nat.le k n` witness) is never used inside
    // the conclusion, so this is a plain (non-dependent) arrow.
    let motive = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let h_ty = d.le(k, n);
        let mrk = d.const_app(p.max_range, &[f, k]);
        let mrnp = d.const_app(p.max_range, &[g, np]);
        let concl = cle(d, p, mrk, mrnp);
        d.arrow(h_ty, concl)
    };

    let proof = d.induct(
        &motive,
        &|d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            let h0_fv = d.fresh_fvar();
            let h0 = d.kernel().fvar(h0_fv);
            let h0_ty = d.le(zero_n, n);

            let f0 = d.apply(f, &[zero_n]);
            let e0 = d.apply(e, &[zero_n]);
            let g_e0 = d.apply(g, &[e0]);
            let mrnp = d.const_app(p.max_range, &[g, np]);

            let heq0 = d.apply(heq, &[zero_n, h0]);
            let he0 = d.apply(hbound, &[zero_n, h0]);
            let ub0 = d.lemma(p.max_range_ub, &[g, np, e0, he0]);
            let symm0 = d.lemma(p.equiv_symm, &[f0, g_e0, heq0]);
            let refl_mrnp = d.lemma(p.equiv_refl, &[mrnp]);
            let result0 = d.lemma(p.le_congr, &[g_e0, f0, mrnp, mrnp, symm0, refl_mrnp, ub0]);

            d.lam_fv(h0_fv, h0_ty, result0)
        },
        &|d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let sj = d.succ(j);
            let hsj_fv = d.fresh_fvar();
            let hsj = d.kernel().fvar(hsj_fv);
            let hsj_ty = d.le(sj, n);

            let le_succ_j = d.lemma(p.rat.int.nat.le_succ, &[j]);
            let hj = d.lemma(p.rat.int.nat.le_trans, &[j, sj, n, le_succ_j, hsj]);
            let ih_hj = d.apply(ih, &[hj]);

            let fsj = d.apply(f, &[sj]);
            let esj = d.apply(e, &[sj]);
            let g_esj = d.apply(g, &[esj]);
            let mrj = d.const_app(p.max_range, &[f, j]);
            let mrnp = d.const_app(p.max_range, &[g, np]);

            let heq_sj = d.apply(heq, &[sj, hsj]);
            let he_sj = d.apply(hbound, &[sj, hsj]);
            let ub_sj = d.lemma(p.max_range_ub, &[g, np, esj, he_sj]);
            let symm_sj = d.lemma(p.equiv_symm, &[fsj, g_esj, heq_sj]);
            let refl_mrnp = d.lemma(p.equiv_refl, &[mrnp]);
            let fsj_le = d.lemma(
                p.le_congr,
                &[g_esj, fsj, mrnp, mrnp, symm_sj, refl_mrnp, ub_sj],
            );

            let combine = d.lemma(p.max_le, &[mrj, fsj, mrnp, ih_hj, fsj_le]);
            d.lam_fv(hsj_fv, hsj_ty, combine)
        },
        n,
    );

    let le_refl_n = d.lemma(p.rat.int.nat.le_refl, &[n]);
    let value_body = d.apply(proof, &[le_refl_n]);

    let mrn = d.const_app(p.max_range, &[f, n]);
    let mrnp_final = d.const_app(p.max_range, &[g, np]);
    let conclusion = cle(d, p, mrn, mrnp_final);

    let ty = {
        let out = d.pi_fv(heq_fv, heq_ty, conclusion);
        let out = d.pi_fv(hbound_fv, hbound_ty, out);
        let out = d.pi_fv(e_fv, nat_fn_ty, out);
        let out = d.pi_fv(np_fv, nat, out);
        let out = d.pi_fv(n_fv, nat, out);
        let out = d.pi_fv(g_fv, fn_ty, out);
        d.pi_fv(f_fv, fn_ty, out)
    };
    let value = {
        let out = d.lam_fv(heq_fv, heq_ty, value_body);
        let out = d.lam_fv(hbound_fv, hbound_ty, out);
        let out = d.lam_fv(e_fv, nat_fn_ty, out);
        let out = d.lam_fv(np_fv, nat, out);
        let out = d.lam_fv(n_fv, nat, out);
        let out = d.lam_fv(g_fv, fn_ty, out);
        d.lam_fv(f_fv, fn_ty, out)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_range_transport,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.maxRange_transport` alone (a one-declaration `BuildStep`,
/// mirroring the shape of every other single-theorem step in this file's
/// `STEPS` table entries).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_max_range_transport(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_max_range_transport_thm(d, p)
}

// ---------------------------------------------------------------------------
// `CReal.meshLevelCount` -- the geometric (doubling) mesh-count schedule
// route 2's nested refinement runs on. See this module's own documentation,
// "Route 2 is the one to pick up", for why doubling (rather than an
// arbitrary refinement factor) is what makes the coarse-in-fine embedding
// need only closed-form index SCALING (`Rat.natDivSucc_scale`/
// `nat_div_succ_mul`) and no `Nat.div`/bucket-index search.
// ---------------------------------------------------------------------------

/// `CReal.meshLevelCount : Nat → Nat`, `meshLevelCount 0 := 0`, `meshLevelCount
/// (succ j) := succ (add (meshLevelCount j) (meshLevelCount j))` — i.e.
/// `meshLevelCount j = 2^j − 1` (a `mesh_level_count(j)+1`-point mesh has
/// `2^j` points), built additively (`add x x` rather than `mul 2 x`) so no
/// `Nat.mul` dependency is needed for this one recursion. Declared under the
/// `creal` namespace (a [`CRealPrelude`] field) even though its VALUE is pure
/// `Nat → Nat`, because every consumer of it lives in this file's later
/// `CReal`-level construction — mirrors [`declare_max_range_def`]'s own
/// `Nat.rec` shape, minus the `f` parameter (this recursion carries no
/// external function, only the level index itself).
fn declare_mesh_level_count_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let nat_add = d.prelude().add;

    let motive = d.kernel().lam(anon, nat, nat, crate::BinderInfo::Default);
    let minor_zero = d.zero();
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let doubled = d.const_app(nat_add, &[ih, ih]);
        let body = d.succ(doubled);
        let inner = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let value_body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = d.lam_fv(n_fv, nat, value_body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mesh_level_count,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// `CReal.meshLevelCount_zero : Eq Nat (meshLevelCount Nat.zero) Nat.zero` and
/// `CReal.meshLevelCount_succ : ∀ j, Eq Nat (meshLevelCount (succ j)) (add
/// (meshLevelCount j) (meshLevelCount j)).succ` — both close by `Eq.refl`
/// alone, the same reason [`declare_max_range_equations`]'s two equations do
/// (`meshLevelCount`'s `Nat.rec` application ι-reduces on both minor
/// premises).
fn declare_mesh_level_count_equations(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_add = d.prelude().add;
    let one = d.level_one();
    let logic = p.rat.int.logic;

    // meshLevelCount_zero : Eq Nat (meshLevelCount zero) zero.
    {
        let zero_n = d.zero();
        let lhs = d.const_app(p.mesh_level_count, &[zero_n]);
        let eq = d.kernel().const_(logic.eq, vec![one]);
        let stmt = d.apply(eq, &[nat, lhs, zero_n]);
        let refl = d.kernel().const_(logic.eq_refl, vec![one]);
        let value = d.apply(refl, &[nat, zero_n]);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.mesh_level_count_zero,
            uparams: vec![],
            ty: stmt,
            value,
        })?;
    }

    // meshLevelCount_succ : ∀ j,
    //   Eq Nat (meshLevelCount (succ j)) (succ (add (meshLevelCount j)
    //     (meshLevelCount j))).
    {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sj = d.succ(j);
        let lhs = d.const_app(p.mesh_level_count, &[sj]);
        let mlc_j = d.const_app(p.mesh_level_count, &[j]);
        let doubled = d.const_app(nat_add, &[mlc_j, mlc_j]);
        let rhs = d.succ(doubled);
        let eq = d.kernel().const_(logic.eq, vec![one]);
        let stmt_inner = d.apply(eq, &[nat, lhs, rhs]);
        let refl = d.kernel().const_(logic.eq_refl, vec![one]);
        let proof_inner = d.apply(refl, &[nat, rhs]);
        let ty = d.pi_fv(j_fv, nat, stmt_inner);
        let value = d.lam_fv(j_fv, nat, proof_inner);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.mesh_level_count_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// Land `CReal.meshLevelCount` and its two defining equations.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_level_count(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_level_count_def(d, p)?;
    declare_mesh_level_count_equations(d, p)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `CReal.meshMax` -- the level-`j` mesh maximum: `maxRange` sampled over the
// `meshLevelCount j`-point mesh of `[a, b]`.
// ---------------------------------------------------------------------------

/// `CReal.mul x y` -- mirrors the `cmul` private to several sibling files
/// (`trig.rs`, `integral.rs`, …), re-derived here rather than imported per
/// this development's own convention (see [`creal_eq`]'s doc comment).
fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

/// `CReal.neg x` -- mirrors sibling files' private `cneg`.
fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

/// `add (mul (b + (neg a)) (embed (Rat.natDivSucc 1 m)))` — the mesh width
/// `Δ = (b − a)/(m + 1)`, the SAME formula and SAME total-in-`m` design
/// `integral.rs`'s own private `delta_of` uses (see that file's own doc
/// comment for why no `CReal.inv`/`PosBound` is needed); re-derived here
/// rather than imported, per this development's convention.
fn mesh_delta(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, m: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_real = embed(d, p, frac);
    cmul(d, p, width, frac_real)
}

/// `add a (mul (ofNat i) delta)` — the `i`-th LEFT sample point `a + i·Δ`.
/// Mirrors `integral.rs`'s own private `sample_point`, re-derived here per
/// this development's convention.
fn mesh_sample_point(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    delta: ExprId,
    i: ExprId,
) -> ExprId {
    let oi = d.const_app(p.of_nat, &[i]);
    let shift = cmul(d, p, oi, delta);
    cadd(d, p, a, shift)
}

/// `(CReal → CReal) → CReal → CReal → Nat → CReal`.
fn mesh_max_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let over_j = d.arrow(nat, carrier);
    let over_b = d.arrow(carrier, over_j);
    let over_a = d.arrow(carrier, over_b);
    d.arrow(func_ty, over_a)
}

/// `CReal.meshMax : (CReal → CReal) → CReal → CReal → Nat → CReal :=
/// fun F a b j => maxRange (fun i => F (meshSamplePoint a (meshDelta a b
/// (meshLevelCount j)) i)) (meshLevelCount j)` — the level-`j` mesh maximum:
/// `max_{i ≤ meshLevelCount j} F(a + i·Δⱼ)`, `Δⱼ := (b−a)/(meshLevelCount j +
/// 1)`. Building block for `CReal.supOn` (this module's own documentation):
/// route 2's telescoping construction produces `supOn` as `CReal.mk` on the
/// sequence `fun j => meshMax F a b j` (or a `speedup` of it), once the
/// regularity estimate lands.
fn declare_mesh_max_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let m = d.const_app(p.mesh_level_count, &[j]);
    let delta = mesh_delta(d, p, a, b, m);

    // The maxRange sampling function: fun i => F (meshSamplePoint a delta i).
    let sampler = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = mesh_sample_point(d, p, a, delta, i);
        let fx = d.apply(f, &[sp]);
        d.lam_fv(i_fv, nat, fx)
    };
    let body = d.const_app(p.max_range, &[sampler, m]);

    let value = {
        let with_j = d.lam_fv(j_fv, nat, body);
        let with_b = d.lam_fv(b_fv, carrier, with_j);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(f_fv, func_ty, with_a)
    };
    let ty = mesh_max_ty(d, p);
    let _ = anon;
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mesh_max,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// Land `CReal.meshMax`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_max(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_mesh_max_def(d, p)
}

// ---------------------------------------------------------------------------
// `CReal.meshMax_step_le` -- rung 3, the order half: adjacent mesh levels are
// ordered, for a function uniformly continuous on `[a, b]`. See this
// module's own documentation, "Rung 3, the order half", and the correction
// to it recorded there: this needs `UniformlyContinuousOn F a b` and `le a
// b` after all (`F` applied to two `Equiv`-but-not-equal mesh points needs
// `F` to respect `Equiv`, which is exactly
// [`CRealPrelude::congr_of_uniformly_continuous`] and is FALSE for an
// arbitrary `F` with no continuity hypothesis).
// ---------------------------------------------------------------------------

/// `Eq Nat (mul (Nat.succ (Nat.succ Nat.zero)) m) (add m m)` -- `2·m = m + m`,
/// built from `Nat.succ_mul` (`mul (succ n) m = add (mul n m) m`, at `n :=
/// 1`) and `Nat.one_mul`, exactly the pattern `nat_prelude/factorization.rs`
/// uses for the same identity (re-derived here per this development's
/// convention of not importing another file's private helper).
fn nat_two_mul_eq_add(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let nat_p = p.rat.int.nat;
    let one_v = d.num(1);
    let sm = d.lemma(nat_p.succ_mul, &[one_v, m]);
    // sm : Eq (mul (succ one_v) m) (add (mul one_v m) m) -- LHS is `mul (num
    // 2) m` since `succ one_v` and `num 2` are the same interned term.
    let one_mul_m = d.lemma(nat_p.one_mul, &[m]); // Eq (mul one_v m) m
    let one_m = NatOps::mul(d, one_v, m);
    let cong_add = NatOps::congr(d, one_m, m, one_mul_m, &|d, t| NatOps::add(d, t, m));
    // cong_add : Eq (add one_m m) (add m m)
    let add_one_m_m = NatOps::add(d, one_m, m);
    let m_m = NatOps::add(d, m, m);
    let two_v = d.num(2);
    let two_m = NatOps::mul(d, two_v, m);
    NatOps::trans(d, two_m, add_one_m_m, m_m, sm, cong_add)
}

/// `Equiv (add Δⱼ' Δⱼ') Δⱼ`, where `Δⱼ := meshDelta a b (meshLevelCount j)`
/// and `Δⱼ' := meshDelta a b (meshLevelCount (Nat.succ j))` -- the mesh width
/// exactly halves from level `j` to level `j+1`.
///
/// Rat-level core: `natDivSucc 1 (meshLevelCount (succ j)) + natDivSucc 1
/// (meshLevelCount (succ j)) = natDivSucc 1 (meshLevelCount j)`, via
/// `Rat.natDivSucc_add` (fusing the sum into `natDivSucc 2 …`) then
/// `Rat.natDivSucc_halve` (`natDivSucc 2 (succ (mul 2 m)) = natDivSucc 1 m`)
/// rewritten along [`nat_two_mul_eq_add`] to replace the multiplicative
/// index `succ (mul 2 m)` with the additive one `succ (add m m)` --
/// `meshLevelCount (succ j)`'s own ι-reduction, since `meshLevelCount` is
/// built additively (`add x x`, not `mul 2 x`, per this file's own
/// `meshLevelCount` documentation). Lifted to `CReal` via `CReal.ofRat_add`
/// and `CReal.left_distrib`.
fn mesh_delta_halve(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    j: ExprId,
) -> ExprId {
    let rat = p.rat;
    let mlc_j = d.const_app(p.mesh_level_count, &[j]);
    let sj = d.succ(j);
    let mlc_sj = d.const_app(p.mesh_level_count, &[sj]);

    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let q = d.const_app(rat.nat_div_succ, &[one_nat, mlc_sj]);
    let target_rat = d.const_app(rat.nat_div_succ, &[one_nat, mlc_j]);

    // Rat level: Eq Rat (radd q q) target_rat.
    let add_fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, mlc_sj]);
    // add_fuse : Eq Rat (radd q q) (natDivSucc (add 1 1) mlc_sj)
    let radd_qq = radd(d, q, q);
    let one_plus_one = NatOps::add(d, one_nat, one_nat);
    let fused_idx = d.const_app(rat.nat_div_succ, &[one_plus_one, mlc_sj]);

    let two_mul_eq = nat_two_mul_eq_add(d, p, mlc_j); // Eq Nat (mul 2 mlc_j) (add mlc_j mlc_j)
    let mul2mlcj = NatOps::mul(d, two_nat, mlc_j);
    let addmlcjmlcj = NatOps::add(d, mlc_j, mlc_j);
    let midx = d.succ(mul2mlcj);
    let ridx = d.succ(addmlcjmlcj);
    let bridge_nat = NatOps::congr(d, mul2mlcj, addmlcjmlcj, two_mul_eq, &|d, t| d.succ(t));
    // bridge_nat : Eq Nat midx ridx

    let halve = d.lemma(rat.nat_div_succ_halve, &[mlc_j]); // Eq Rat (natDivSucc 2 midx) target_rat
    let halve_at_ridx = nat_rewrite_prop(d, midx, ridx, bridge_nat, halve, &|d, t| {
        let lhs = d.const_app(rat.nat_div_succ, &[two_nat, t]);
        req(d, lhs, target_rat)
    });
    // halve_at_ridx : Eq Rat (natDivSucc 2 ridx) target_rat -- ridx is defeq
    // mlc_sj (meshLevelCount's own ι-reduction), so this and `add_fuse`
    // chain at the shared middle term up to defeq.
    let rat_eq = rtrans(d, radd_qq, fused_idx, target_rat, add_fuse, halve_at_ridx);
    // rat_eq : Eq Rat (radd q q) target_rat

    // Lift to CReal: Equiv (add (embed q) (embed q)) (embed target_rat).
    let of_rat_add_step = d.lemma(p.of_rat_add, &[q, q]);
    // of_rat_add_step : Equiv (add (embed q) (embed q)) (embed (radd q q))
    let embed_level = rat_eq_rewrite(d, radd_qq, target_rat, rat_eq, of_rat_add_step, &|d, t| {
        let embed_q = embed(d, p, q);
        let sum_real = cadd(d, p, embed_q, embed_q);
        let embedded = embed(d, p, t);
        cequiv(d, p, sum_real, embedded)
    });
    // embed_level : Equiv (add (embed q) (embed q)) (embed target_rat)

    // Multiply through by the shared width factor.
    let delta_j = mesh_delta(d, p, a, b, mlc_j);
    let delta_sj = mesh_delta(d, p, a, b, mlc_sj);
    let width = {
        let na = cneg(d, p, a);
        cadd(d, p, b, na)
    };
    let embed_q = embed(d, p, q);
    let embed_target = embed(d, p, target_rat);
    let sum_embed = cadd(d, p, embed_q, embed_q);

    let refl_width = d.lemma(p.equiv_refl, &[width]);
    let mul_congr_step = d.lemma(
        p.mul_congr,
        &[
            width,
            width,
            sum_embed,
            embed_target,
            refl_width,
            embed_level,
        ],
    );
    // mul_congr_step : Equiv (mul width sum_embed) (mul width embed_target)
    //                = Equiv (mul width sum_embed) delta_j

    let dist_left = d.lemma(p.left_distrib, &[width, embed_q, embed_q]);
    // dist_left : Equiv (mul width sum_embed) (add (mul width embed_q) (mul width embed_q))
    //           = Equiv (mul width sum_embed) (add delta_sj delta_sj)
    let mul_width_sum = cmul(d, p, width, sum_embed);
    let add_delta_sj_delta_sj = cadd(d, p, delta_sj, delta_sj);
    let dist_left_symm = d.lemma(
        p.equiv_symm,
        &[mul_width_sum, add_delta_sj_delta_sj, dist_left],
    );
    // dist_left_symm : Equiv (add delta_sj delta_sj) (mul width sum_embed)

    d.lemma(
        p.equiv_trans,
        &[
            add_delta_sj_delta_sj,
            mul_width_sum,
            delta_j,
            dist_left_symm,
            mul_congr_step,
        ],
    )
    // : Equiv (add delta_sj delta_sj) delta_j
}

/// `Equiv (meshSamplePoint a Δⱼ i) (meshSamplePoint a Δⱼ' (add i i))` -- the
/// level-`j` coarse sample point at index `i` is `CReal.Equiv` to the
/// level-`(j+1)` fine sample point at index `2i` (built additively as `add i
/// i`). Route: `ofNat (add i i) ~ add (ofNat i) (ofNat i)`
/// ([`CRealPrelude::of_nat_add`]), distribute across `Δⱼ'`
/// ([`right_distrib`]), refactor the resulting sum back through `ofNat i`
/// ([`CRealPrelude::left_distrib`], reversed), close the `Δⱼ' + Δⱼ' ~ Δⱼ`
/// gap via [`mesh_delta_halve`], then lift across the shared `a +` via
/// [`CRealPrelude::add_congr`].
fn mesh_sample_transport(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    j: ExprId,
    i: ExprId,
) -> ExprId {
    let mlc_j = d.const_app(p.mesh_level_count, &[j]);
    let sj = d.succ(j);
    let mlc_sj = d.const_app(p.mesh_level_count, &[sj]);
    let delta_j = mesh_delta(d, p, a, b, mlc_j);
    let delta_sj = mesh_delta(d, p, a, b, mlc_sj);
    let ii = NatOps::add(d, i, i);

    let of_nat_i = d.const_app(p.of_nat, &[i]);
    let of_nat_ii = d.const_app(p.of_nat, &[ii]);
    let sum_oi = cadd(d, p, of_nat_i, of_nat_i);

    let of_nat_add_step = d.lemma(p.of_nat_add, &[i, i]);
    // of_nat_add_step : Equiv (ofNat (add i i)) (add (ofNat i) (ofNat i))

    let refl_delta_sj = d.lemma(p.equiv_refl, &[delta_sj]);
    let term_a = cmul(d, p, of_nat_ii, delta_sj); // ofNat(i+i) * delta_sj
    let term_b = cmul(d, p, sum_oi, delta_sj);
    let step2 = d.lemma(
        p.mul_congr,
        &[
            of_nat_ii,
            sum_oi,
            delta_sj,
            delta_sj,
            of_nat_add_step,
            refl_delta_sj,
        ],
    );
    // step2 : Equiv term_a term_b

    let step3 = right_distrib(d, p, of_nat_i, of_nat_i, delta_sj);
    // step3 : Equiv term_b (add (mul of_nat_i delta_sj) (mul of_nat_i delta_sj))
    let oi_delta_sj = cmul(d, p, of_nat_i, delta_sj);
    let term_c = cadd(d, p, oi_delta_sj, oi_delta_sj);
    let step23 = d.lemma(p.equiv_trans, &[term_a, term_b, term_c, step2, step3]);
    // step23 : Equiv term_a term_c

    let sum_delta_sj = cadd(d, p, delta_sj, delta_sj);
    let oi_sum_delta_sj = cmul(d, p, of_nat_i, sum_delta_sj);
    let dist2 = d.lemma(p.left_distrib, &[of_nat_i, delta_sj, delta_sj]);
    // dist2 : Equiv oi_sum_delta_sj term_c
    let dist2_symm = d.lemma(p.equiv_symm, &[oi_sum_delta_sj, term_c, dist2]);
    // dist2_symm : Equiv term_c oi_sum_delta_sj

    let step234 = d.lemma(
        p.equiv_trans,
        &[term_a, term_c, oi_sum_delta_sj, step23, dist2_symm],
    );
    // step234 : Equiv term_a oi_sum_delta_sj

    let halve = mesh_delta_halve(d, p, a, b, j); // Equiv sum_delta_sj delta_j
    let refl_oi = d.lemma(p.equiv_refl, &[of_nat_i]);
    let term_final = cmul(d, p, of_nat_i, delta_j); // ofNat(i) * delta_j
    let step6 = d.lemma(
        p.mul_congr,
        &[of_nat_i, of_nat_i, sum_delta_sj, delta_j, refl_oi, halve],
    );
    // step6 : Equiv oi_sum_delta_sj term_final

    let step2346 = d.lemma(
        p.equiv_trans,
        &[term_a, oi_sum_delta_sj, term_final, step234, step6],
    );
    // step2346 : Equiv term_a term_final

    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let step_final = d.lemma(p.add_congr, &[a, a, term_a, term_final, refl_a, step2346]);
    // step_final : Equiv (add a term_a) (add a term_final)
    //            = Equiv (meshSamplePoint a delta_sj ii) (meshSamplePoint a delta_j i)

    let sp_sj = mesh_sample_point(d, p, a, delta_sj, ii);
    let sp_j = mesh_sample_point(d, p, a, delta_j, i);
    d.lemma(p.equiv_symm, &[sp_sj, sp_j, step_final])
    // : Equiv sp_j sp_sj
}

/// `CReal.meshMax_step_le : ∀ F a b j, UniformlyContinuousOn F a b → le a b →
/// le (meshMax F a b j) (meshMax F a b (Nat.succ j))` -- rung 3.
///
/// Instantiates [`CRealPrelude::max_range_transport`] at the two mesh
/// samplers (`f := fun i => F (meshSamplePoint a Δⱼ i)`, `g := fun i => F
/// (meshSamplePoint a Δⱼ' i)`), bounds `n := meshLevelCount j`, `n' :=
/// meshLevelCount (succ j)`, and index embedding `e := fun i => add i i`.
/// `hbound` is pure `Nat` order algebra (`add_le_add_left/_right` plus
/// `le_succ`, `le_trans`); `heq` places both sample points in `[a, b]` via
/// [`CRealPrelude::riemann_sample_in_bounds`] (the same mesh-point shape
/// `riemannSum` uses) and closes with
/// [`CRealPrelude::congr_of_uniformly_continuous`] against
/// [`mesh_sample_transport`]'s point-level `Equiv`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_mesh_max_step_le_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let mlc_j = d.const_app(p.mesh_level_count, &[j]);
    let sj = d.succ(j);
    let mlc_sj = d.const_app(p.mesh_level_count, &[sj]);
    let delta_j = mesh_delta(d, p, a, b, mlc_j);
    let delta_sj = mesh_delta(d, p, a, b, mlc_sj);

    let f_sampler = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = mesh_sample_point(d, p, a, delta_j, i);
        let fx = d.apply(f, &[sp]);
        d.lam_fv(i_fv, nat, fx)
    };
    let g_sampler = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = mesh_sample_point(d, p, a, delta_sj, i);
        let fx = d.apply(f, &[sp]);
        d.lam_fv(i_fv, nat, fx)
    };
    let e_fn = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ei = NatOps::add(d, i, i);
        d.lam_fv(i_fv, nat, ei)
    };

    // hbound : ∀ i, Nat.le i mlc_j → Nat.le (add i i) mlc_sj.
    let hbound = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.le(i, mlc_j);

        let step1 = d.lemma(nat_p.add_le_add_right, &[i, i, mlc_j, hi]);
        // step1 : Le (add i i) (add mlc_j i)
        let step2 = d.lemma(nat_p.add_le_add_left, &[mlc_j, i, mlc_j, hi]);
        // step2 : Le (add mlc_j i) (add mlc_j mlc_j)
        let ii = NatOps::add(d, i, i);
        let mm = NatOps::add(d, mlc_j, i);
        let mm2 = NatOps::add(d, mlc_j, mlc_j);
        let combined = d.lemma(nat_p.le_trans, &[ii, mm, mm2, step1, step2]);
        let step3 = d.lemma(nat_p.le_succ, &[mm2]);
        let smm2 = d.succ(mm2);
        let final_le = d.lemma(nat_p.le_trans, &[ii, mm2, smm2, combined, step3]);
        // final_le : Le (add i i) (succ (add mlc_j mlc_j)) -- defeq mlc_sj

        let body = d.lam_fv(hi_fv, hi_ty, final_le);
        d.lam_fv(i_fv, nat, body)
    };

    // heq : ∀ i, Nat.le i mlc_j → Equiv (f_sampler i) (g_sampler (add i i)).
    let heq = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.le(i, mlc_j);

        let sp_j = mesh_sample_point(d, p, a, delta_j, i);
        let ii = NatOps::add(d, i, i);
        let sp_sj = mesh_sample_point(d, p, a, delta_sj, ii);

        let hlt_i = d.lemma(nat_p.lt_succ_of_le, &[i, mlc_j, hi]);
        let and_j = d.const_app(p.riemann_sample_in_bounds, &[a, b, mlc_j, i, hab, hlt_i]);
        let a_le_spj = cle(d, p, a, sp_j);
        let spj_le_b = cle(d, p, sp_j, b);
        let hax_j = d.const_app(logic.and_left, &[a_le_spj, spj_le_b, and_j]);
        let hxb_j = d.const_app(logic.and_right, &[a_le_spj, spj_le_b, and_j]);

        let hbound_i = d.apply(hbound, &[i, hi]);
        let hlt_ii = d.lemma(nat_p.lt_succ_of_le, &[ii, mlc_sj, hbound_i]);
        let and_sj = d.const_app(p.riemann_sample_in_bounds, &[a, b, mlc_sj, ii, hab, hlt_ii]);
        let a_le_spsj = cle(d, p, a, sp_sj);
        let spsj_le_b = cle(d, p, sp_sj, b);
        let hay_sj = d.const_app(logic.and_left, &[a_le_spsj, spsj_le_b, and_sj]);
        let hyb_sj = d.const_app(logic.and_right, &[a_le_spsj, spsj_le_b, and_sj]);

        let point_equiv = mesh_sample_transport(d, p, a, b, j, i);

        let concl = d.lemma(
            p.congr_of_uniformly_continuous,
            &[
                f,
                a,
                b,
                u,
                sp_j,
                sp_sj,
                hax_j,
                hxb_j,
                hay_sj,
                hyb_sj,
                point_equiv,
            ],
        );

        let body = d.lam_fv(hi_fv, hi_ty, concl);
        d.lam_fv(i_fv, nat, body)
    };

    let transport_applied = d.const_app(
        p.max_range_transport,
        &[f_sampler, g_sampler, mlc_j, mlc_sj, e_fn, hbound, heq],
    );

    let mesh_j = d.const_app(p.mesh_max, &[f, a, b, j]);
    let mesh_sj = d.const_app(p.mesh_max, &[f, a, b, sj]);
    let conclusion = cle(d, p, mesh_j, mesh_sj);

    let ty = {
        let after_hab = d.arrow(hab_ty, conclusion);
        let after_u = d.arrow(u_ty, after_hab);
        let over_j = d.pi_fv(j_fv, nat, after_u);
        let over_b = d.pi_fv(b_fv, carrier, over_j);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, func_ty, over_a)
    };
    let value = {
        let after_hab = d.lam_fv(hab_fv, hab_ty, transport_applied);
        let after_u = d.lam_fv(u_fv, u_ty, after_hab);
        let over_j = d.lam_fv(j_fv, nat, after_u);
        let over_b = d.lam_fv(b_fv, carrier, over_j);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, func_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_max_step_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.meshMax_step_le` alone (a one-declaration `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_max_step_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_max_step_le_thm(d, p)
}

/// `CReal.meshMax_mono : ∀ F a b, UniformlyContinuousOn F a b → le a b → ∀ j
/// j', Nat.le j j' → le (meshMax F a b j) (meshMax F a b j')` -- rung 4,
/// general monotonicity, for free from rung 3 via
/// [`CRealPrelude::mono_of_le_succ`] applied to `fun k => meshMax F a b k`
/// with [`declare_mesh_max_step_le`]'s theorem as the adjacent step --
/// EXACTLY [`declare_max_range_mono`]'s own construction, one level up (`F`,
/// `a`, `b`, `u`, `hab` closed over rather than varying).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_mesh_max_mono_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let mesh_f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.mesh_max, &[f, a, b, k]);
        d.lam_fv(k_fv, nat, body)
    };
    let adjacent = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.const_app(p.mesh_max_step_le, &[f, a, b, n, u, hab]);
        d.lam_fv(n_fv, nat, body)
    };
    let mono = d.const_app(p.mono_of_le_succ, &[mesh_f, adjacent]);

    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let jp_fv = d.fresh_fvar();
    let jp = d.kernel().fvar(jp_fv);
    let hjj_fv = d.fresh_fvar();
    let hjj = d.kernel().fvar(hjj_fv);
    let hjj_ty = d.le(j, jp);
    let applied = d.apply(mono, &[j, jp, hjj]);

    let mesh_j = d.const_app(p.mesh_max, &[f, a, b, j]);
    let mesh_jp = d.const_app(p.mesh_max, &[f, a, b, jp]);
    let conclusion = cle(d, p, mesh_j, mesh_jp);

    let ty = {
        let anon = d.anon_name();
        let out = d
            .kernel()
            .pi(anon, hjj_ty, conclusion, crate::BinderInfo::Default);
        let out = d.pi_fv(jp_fv, nat, out);
        let out = d.pi_fv(j_fv, nat, out);
        let out = d.arrow(hab_ty, out);
        let out = d.arrow(u_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(hjj_fv, hjj_ty, applied);
        let out = d.lam_fv(jp_fv, nat, out);
        let out = d.lam_fv(j_fv, nat, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_max_mono,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.meshMax_mono` alone (a one-declaration `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_max_mono(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_max_mono_thm(d, p)
}

// ---------------------------------------------------------------------------
// `CReal.expOfModulus` / `CReal.trueExpOfModulus` -- rung 5, the
// accuracy-selection scheme (where continuity's quantitative content, the
// modulus, first enters). See this module's own documentation, "Rung 5, the
// accuracy-selection scheme", for the harmonic-vs-summable finding this
// schedule exists to fix.
// ---------------------------------------------------------------------------

/// `CReal.expOfModulus : (Nat → Nat) → Nat → Nat := fun m k => Nat.size (m
/// (meshLevelCount k))` — the per-level accuracy request: `Nat.size` turns
/// an arbitrary modulus value `m (meshLevelCount k)` into a power-of-two
/// EXPONENT that dominates it via `Nat.lt_pow_size : ∀ n, Lt n (pow 2 (size
/// n))`, with no `Nat.div`/search. Left generic over `m : Nat → Nat` rather
/// than tied to a specific `UniformlyContinuousOn` witness — callers apply
/// it at `m := UniformlyContinuousOn.modulus F a b u` — so this and
/// [`declare_true_exp_of_modulus`] are pure `Nat`-level machinery, reusable
/// beyond this file's own `F`/`a`/`b`.
fn declare_exp_of_modulus_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);
    let nat_p = p.rat.int.nat;

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let mlc_k = d.const_app(p.mesh_level_count, &[k]);
    let m_at = d.apply(m, &[mlc_k]);
    let sized = d.const_app(nat_p.size, &[m_at]);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, sized);
        d.lam_fv(m_fv, nat_fn, with_k)
    };
    let ty = {
        let over_k = d.arrow(nat, nat);
        d.arrow(nat_fn, over_k)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.exp_of_modulus,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// Land `CReal.expOfModulus` alone (a one-declaration `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_exp_of_modulus(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_exp_of_modulus_def(d, p)
}

/// `CReal.trueExpOfModulus : (Nat → Nat) → Nat → Nat`, `Nat.rec`-structured
/// on the level and closed over `m` (mirrors [`declare_max_range_def`]'s own
/// shape, one type down): `trueExpOfModulus m 0 := expOfModulus m 0`,
/// `trueExpOfModulus m (succ k) := add (trueExpOfModulus m k) (expOfModulus
/// m (succ k))` — the running-sum accumulator that forces monotonicity onto
/// [`declare_exp_of_modulus_def`]'s own not-necessarily-monotone sequence
/// (an arbitrary modulus need not itself be monotone). Built with
/// `Nat.add`, never `Nat.max`: **this kernel's `Nat` prelude has no
/// `Nat.max`**.
fn declare_true_exp_of_modulus_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);
    let anon = d.anon_name();
    let one_level = d.level_one();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = d.kernel().lam(anon, nat, nat, crate::BinderInfo::Default);
    let zero_n = d.zero();
    let minor_zero = d.const_app(p.exp_of_modulus, &[m, zero_n]);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let sj = d.succ(j);
        let exp_sj = d.const_app(p.exp_of_modulus, &[m, sj]);
        let body = NatOps::add(d, ih, exp_sj);
        let inner = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, k]);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        d.lam_fv(m_fv, nat_fn, with_k)
    };
    let ty = {
        let over_k = d.arrow(nat, nat);
        d.arrow(nat_fn, over_k)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.true_exp_of_modulus,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// `CReal.trueExpOfModulus_zero`/`CReal.trueExpOfModulus_succ`: the defining
/// equations of [`declare_true_exp_of_modulus_def`], each closed by
/// `Eq.refl` alone since `trueExpOfModulus`'s `Nat.rec` application
/// ι-reduces on both minor premises (mirrors
/// [`declare_max_range_equations`]).
fn declare_true_exp_of_modulus_equations(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);

    // trueExpOfModulus_zero : ∀ m,
    //   Eq Nat (trueExpOfModulus m zero) (expOfModulus m zero).
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let zero_n = d.zero();
        let lhs = d.const_app(p.true_exp_of_modulus, &[m, zero_n]);
        let rhs = d.const_app(p.exp_of_modulus, &[m, zero_n]);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        let value = d.lam_fv(m_fv, nat_fn, proof);
        let ty = d.pi_fv(m_fv, nat_fn, stmt);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.true_exp_of_modulus_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // trueExpOfModulus_succ : ∀ m k,
    //   Eq Nat (trueExpOfModulus m (succ k))
    //          (add (trueExpOfModulus m k) (expOfModulus m (succ k))).
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let lhs = d.const_app(p.true_exp_of_modulus, &[m, sk]);
        let te_k = d.const_app(p.true_exp_of_modulus, &[m, k]);
        let exp_sk = d.const_app(p.exp_of_modulus, &[m, sk]);
        let rhs = NatOps::add(d, te_k, exp_sk);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        let value = {
            let with_k = d.lam_fv(k_fv, nat, proof);
            d.lam_fv(m_fv, nat_fn, with_k)
        };
        let ty = {
            let over_k = d.pi_fv(k_fv, nat, stmt);
            d.pi_fv(m_fv, nat_fn, over_k)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.true_exp_of_modulus_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// Land `CReal.trueExpOfModulus` and its two defining equations.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_true_exp_of_modulus(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_true_exp_of_modulus_def(d, p)?;
    declare_true_exp_of_modulus_equations(d, p)
}

/// `CReal.trueExpOfModulus_step_le : ∀ m k, Nat.le (trueExpOfModulus m k)
/// (trueExpOfModulus m (succ k))` — the adjacent-step half of
/// monotonicity. `trueExpOfModulus m (succ k)` ι-reduces to `add
/// (trueExpOfModulus m k) (expOfModulus m (succ k))`
/// ([`declare_true_exp_of_modulus_equations`]'s own `_succ` statement, by
/// that same ι-reduction), and `Nat.le_add_right (trueExpOfModulus m k)
/// (expOfModulus m (succ k))` is already exactly the needed bound — no
/// rewriting needed, only defeq (mirrors the `hbound` step in
/// [`declare_mesh_max_step_le_thm`]).
fn declare_true_exp_of_modulus_step_le_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);
    let nat_p = p.rat.int.nat;

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let te_k = d.const_app(p.true_exp_of_modulus, &[m, k]);
    let sk = d.succ(k);
    let exp_sk = d.const_app(p.exp_of_modulus, &[m, sk]);
    // bound : Le te_k (add te_k exp_sk) -- defeq to Le te_k (trueExpOfModulus m (succ k)).
    let bound = d.lemma(nat_p.le_add_right, &[te_k, exp_sk]);

    let te_sk = d.const_app(p.true_exp_of_modulus, &[m, sk]);
    let conclusion = d.le(te_k, te_sk);

    let ty = {
        let over_k = d.pi_fv(k_fv, nat, conclusion);
        d.pi_fv(m_fv, nat_fn, over_k)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, bound);
        d.lam_fv(m_fv, nat_fn, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.true_exp_of_modulus_step_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.trueExpOfModulus_step_le` alone (a one-declaration
/// `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_true_exp_of_modulus_step_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_true_exp_of_modulus_step_le_thm(d, p)
}

/// `CReal.trueExpOfModulus_mono : ∀ m j j', Nat.le j j' → Nat.le
/// (trueExpOfModulus m j) (trueExpOfModulus m j')` — general monotonicity,
/// free from [`declare_true_exp_of_modulus_step_le`] via
/// `Nat.monotone_of_le_succ` (the `Nat`-level twin of
/// [`CRealPrelude::mono_of_le_succ`]) — EXACTLY
/// [`declare_mesh_max_mono_thm`]'s own construction, one type down
/// (`Nat`-valued rather than `CReal`-valued, so `m` is closed over instead
/// of `F`/`a`/`b`/the continuity witness/`le a b`).
fn declare_true_exp_of_modulus_mono_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);
    let nat_p = p.rat.int.nat;

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let te_f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.true_exp_of_modulus, &[m, k]);
        d.lam_fv(k_fv, nat, body)
    };
    let adjacent = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.const_app(p.true_exp_of_modulus_step_le, &[m, n]);
        d.lam_fv(n_fv, nat, body)
    };
    let mono = d.lemma(nat_p.monotone_of_le_succ, &[te_f, adjacent]);

    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let jp_fv = d.fresh_fvar();
    let jp = d.kernel().fvar(jp_fv);
    let hjj_fv = d.fresh_fvar();
    let hjj = d.kernel().fvar(hjj_fv);
    let hjj_ty = d.le(j, jp);
    let applied = d.apply(mono, &[j, jp, hjj]);

    let te_j = d.const_app(p.true_exp_of_modulus, &[m, j]);
    let te_jp = d.const_app(p.true_exp_of_modulus, &[m, jp]);
    let conclusion = d.le(te_j, te_jp);

    let ty = {
        let anon = d.anon_name();
        let out = d
            .kernel()
            .pi(anon, hjj_ty, conclusion, crate::BinderInfo::Default);
        let out = d.pi_fv(jp_fv, nat, out);
        let out = d.pi_fv(j_fv, nat, out);
        d.pi_fv(m_fv, nat_fn, out)
    };
    let value = {
        let out = d.lam_fv(hjj_fv, hjj_ty, applied);
        let out = d.lam_fv(jp_fv, nat, out);
        let out = d.lam_fv(j_fv, nat, out);
        d.lam_fv(m_fv, nat_fn, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.true_exp_of_modulus_mono,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.trueExpOfModulus_mono` alone (a one-declaration `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_true_exp_of_modulus_mono(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_true_exp_of_modulus_mono_thm(d, p)
}

/// `CReal.expOfModulus_le_trueExpOfModulus : ∀ m k, Nat.le (expOfModulus m
/// k) (trueExpOfModulus m k)` — the accumulator is always at least as fine
/// as the single level it was built to cover (needed by rung 6's per-level
/// gap bound: the modulus's own spec is stated at accuracy request
/// `meshLevelCount k`, i.e. in terms of [`declare_exp_of_modulus_def`]
/// alone, but the mesh actually sampled at level `k` is
/// `meshMax F a b (trueExpOfModulus m k)`).
///
/// Proof by induction on `k` (via [`NatOps::induct`], mirrors
/// [`declare_max_range_self_le`]'s own use of it one type up): the base
/// case is `Nat.le_refl` against [`declare_true_exp_of_modulus_equations`]'s
/// `_zero` ι-reduction (`trueExpOfModulus m 0 ≡ expOfModulus m 0`); the
/// step case needs `Le x (add y x)` from `Nat.le_add_right : Le x (add x
/// y)`, a genuine commute — no `Nat.le_add_left` exists in this kernel's
/// `Nat` prelude — closed by
/// [`crate::rat_prelude::ops::nat_rewrite_prop`] rewriting along
/// `Nat.add_comm x y : Eq Nat (add x y) (add y x)`. The inductive
/// hypothesis is available but unused: the bound holds at `succ k`
/// independently of what held at `k`, since `trueExpOfModulus m (succ k)`
/// always contains `expOfModulus m (succ k)` as an addend by construction.
fn declare_exp_of_modulus_le_true_exp_of_modulus_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);
    let nat_p = p.rat.int.nat;

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let exp_x = d.const_app(p.exp_of_modulus, &[m, x]);
        let te_x = d.const_app(p.true_exp_of_modulus, &[m, x]);
        d.le(exp_x, te_x)
    };

    let proof = d.induct(
        &motive,
        &|d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            let exp0 = d.const_app(p.exp_of_modulus, &[m, zero_n]);
            d.lemma(nat_p.le_refl, &[exp0])
        },
        &|d: &mut IntDev<'_>, j: ExprId, _ih: ExprId| -> ExprId {
            let sj = d.succ(j);
            let x = d.const_app(p.exp_of_modulus, &[m, sj]);
            let y = d.const_app(p.true_exp_of_modulus, &[m, j]);
            let base = d.lemma(nat_p.le_add_right, &[x, y]);
            let hcomm = d.lemma(nat_p.add_comm, &[x, y]);
            let axy = NatOps::add(d, x, y);
            let ayx = NatOps::add(d, y, x);
            nat_rewrite_prop(d, axy, ayx, hcomm, base, &|d, z| d.le(x, z))
        },
        k,
    );

    let stmt = motive(d, k);
    let ty = {
        let inner = d.pi_fv(k_fv, nat, stmt);
        d.pi_fv(m_fv, nat_fn, inner)
    };
    let value = {
        let inner = d.lam_fv(k_fv, nat, proof);
        d.lam_fv(m_fv, nat_fn, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_of_modulus_le_true_exp_of_modulus,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.expOfModulus_le_trueExpOfModulus` alone (a one-declaration
/// `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_exp_of_modulus_le_true_exp_of_modulus(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_exp_of_modulus_le_true_exp_of_modulus_thm(d, p)
}

// ---------------------------------------------------------------------------
// Rung 6, step 1: the MULTI-LEVEL nearest-mesh-point lemma.
//
// `CReal.meshPoint_near_coarse` -- every level-`(j+d)` mesh point, at ANY
// refinement depth `d`, sits inside one level-`j` cell. See the module
// documentation's "Rung 6 re-verified" section for why this, and not the
// constant-multiple corollary, is what blocks `supOn`.
// ---------------------------------------------------------------------------

/// `CReal.zero`.
fn czero_local(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `meshDelta a b (meshLevelCount level)` -- the level-`level` mesh width.
fn level_delta(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, level: ExprId) -> ExprId {
    let m = d.const_app(p.mesh_level_count, &[level]);
    mesh_delta(d, p, a, b, m)
}

/// `meshSamplePoint a (meshDelta a b (meshLevelCount level)) i`.
fn level_point(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    level: ExprId,
    i: ExprId,
) -> ExprId {
    let delta = level_delta(d, p, a, b, level);
    mesh_sample_point(d, p, a, delta, i)
}

/// `Equiv (ofNat (Nat.succ Nat.zero)) one` -- duplicated from `integral.rs`'s
/// and `monotone.rs`'s private `of_nat_one_equiv_local`, per this
/// development's re-derive-rather-than-widen convention.
fn of_nat_one_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let one_rat = d.kernel().const_(rat.one, vec![]);
    let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
    let unit_embed = embed(d, p, unit);
    let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
    rat_eq_rewrite(d, unit, one_rat, unit_eq_one, refl_start, &|d, t| {
        let embedded = embed(d, p, t);
        cequiv(d, p, unit_embed, embedded)
    })
}

/// `Equiv (ofNat (Nat.succ m)) (add (ofNat m) one)` -- duplicated from
/// `integral.rs`'s / `monotone.rs`'s private `of_nat_succ_equiv_local`.
fn of_nat_succ_equiv(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let one_c = d.kernel().const_(p.one, vec![]);

    let m_rat = d.const_app(rat.nat_div_succ, &[m, zero_nat]);
    let one_ratdiv = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let sum_rat = radd(d, m_rat, one_ratdiv);
    let succ_m = d.succ(m);
    let succ_rat = d.const_app(rat.nat_div_succ, &[succ_m, zero_nat]);
    let add_eq = d.lemma(rat.nat_div_succ_add, &[m, one_nat, zero_nat]);

    let of_nat_m = d.const_app(p.of_nat, &[m]);
    let of_nat_1 = d.const_app(p.of_nat, &[one_nat]);
    let of_nat_succ_m = d.const_app(p.of_nat, &[succ_m]);
    let add_of_nat_m_1 = cadd(d, p, of_nat_m, of_nat_1);

    let add_step = d.lemma(p.of_rat_add, &[m_rat, one_ratdiv]);
    let rewritten = rat_eq_rewrite(d, sum_rat, succ_rat, add_eq, add_step, &|d, t| {
        let embedded = embed(d, p, t);
        cequiv(d, p, add_of_nat_m_1, embedded)
    });
    let flipped = d.lemma(p.equiv_symm, &[add_of_nat_m_1, of_nat_succ_m, rewritten]);

    let one_eq = of_nat_one_equiv(d, p);
    let refl_m = d.lemma(p.equiv_refl, &[of_nat_m]);
    let congr_step = d.lemma(
        p.add_congr,
        &[of_nat_m, of_nat_m, of_nat_1, one_c, refl_m, one_eq],
    );
    let add_of_nat_m_one = cadd(d, p, of_nat_m, one_c);
    d.lemma(
        p.equiv_trans,
        &[
            of_nat_succ_m,
            add_of_nat_m_1,
            add_of_nat_m_one,
            flipped,
            congr_step,
        ],
    )
}

/// `Equiv (mul one x) x` -- `mul_comm` then `mul_one`.
fn one_mul_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let one_c = d.kernel().const_(p.one, vec![]);
    let lhs = cmul(d, p, one_c, x);
    let swapped = cmul(d, p, x, one_c);
    let comm = d.lemma(p.mul_comm, &[one_c, x]);
    let trim = d.lemma(p.mul_one, &[x]);
    d.lemma(p.equiv_trans, &[lhs, swapped, x, comm, trim])
}

/// `Equiv (meshSamplePoint a delta (Nat.succ n)) (add (meshSamplePoint a delta
/// n) delta)` -- the mesh advances by exactly one width per index step. Route:
/// [`of_nat_succ_equiv`], [`right_distrib`], [`one_mul_equiv`], then
/// `add_assoc` (reversed) to re-associate the shared `a +`.
fn sample_succ_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    delta: ExprId,
    n: ExprId,
) -> ExprId {
    let one_c = d.kernel().const_(p.one, vec![]);
    let of_nat_n = d.const_app(p.of_nat, &[n]);
    let sn = d.succ(n);
    let of_nat_sn = d.const_app(p.of_nat, &[sn]);
    let sum_on = cadd(d, p, of_nat_n, one_c);

    let s1 = of_nat_succ_equiv(d, p, n);
    let refl_delta = d.lemma(p.equiv_refl, &[delta]);
    let lhs_mul = cmul(d, p, of_nat_sn, delta);
    let mid_mul = cmul(d, p, sum_on, delta);
    let m1 = d.lemma(
        p.mul_congr,
        &[of_nat_sn, sum_on, delta, delta, s1, refl_delta],
    );
    // m1 : Equiv (mul (ofNat (succ n)) delta) (mul (add (ofNat n) one) delta)

    let m2 = right_distrib(d, p, of_nat_n, one_c, delta);
    let on_delta = cmul(d, p, of_nat_n, delta);
    let one_delta = cmul(d, p, one_c, delta);
    let split = cadd(d, p, on_delta, one_delta);
    // m2 : Equiv mid_mul split

    let m3 = one_mul_equiv(d, p, delta);
    let refl_on_delta = d.lemma(p.equiv_refl, &[on_delta]);
    let m4 = d.lemma(
        p.add_congr,
        &[on_delta, on_delta, one_delta, delta, refl_on_delta, m3],
    );
    let trimmed = cadd(d, p, on_delta, delta);
    // m4 : Equiv split trimmed

    let chain1 = d.lemma(p.equiv_trans, &[lhs_mul, mid_mul, split, m1, m2]);
    let chain2 = d.lemma(p.equiv_trans, &[lhs_mul, split, trimmed, chain1, m4]);
    // chain2 : Equiv (mul (ofNat (succ n)) delta) (add (mul (ofNat n) delta) delta)

    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let lifted = d.lemma(p.add_congr, &[a, a, lhs_mul, trimmed, refl_a, chain2]);
    let sp_succ = cadd(d, p, a, lhs_mul);
    let nested = cadd(d, p, a, trimmed);
    // lifted : Equiv sp_succ nested

    let assoc = d.lemma(p.add_assoc, &[a, on_delta, delta]);
    let sp_n = cadd(d, p, a, on_delta);
    let flat = cadd(d, p, sp_n, delta);
    let assoc_symm = d.lemma(p.equiv_symm, &[flat, nested, assoc]);
    // assoc_symm : Equiv nested flat

    d.lemma(p.equiv_trans, &[sp_succ, nested, flat, lifted, assoc_symm])
}

/// `le x (add x w)` given `hw : le zero w` -- duplicated from `integral.rs`'s
/// private `shift_le_of_nonneg`.
fn shift_le_of_nonneg_local(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    w: ExprId,
    hw: ExprId,
) -> ExprId {
    let zero_c = czero_local(d, p);
    let refl_x = d.lemma(p.le_refl, &[x]);
    let grown = d.lemma(p.add_le_add, &[x, x, zero_c, w, refl_x, hw]);
    let padded = cadd(d, p, x, zero_c);
    let target = cadd(d, p, x, w);
    let trim = d.lemma(p.add_zero, &[x]);
    let refl_target = d.lemma(p.equiv_refl, &[target]);
    d.lemma(
        p.le_congr,
        &[padded, x, target, target, trim, refl_target, grown],
    )
}

/// `le zero (meshDelta a b m)`, given `hab : le a b` -- duplicated from
/// `integral.rs`'s private `delta_nonneg_of` (returns just the proof; the
/// delta itself is rebuilt by [`mesh_delta`] at each call site).
fn mesh_delta_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    m: ExprId,
    hab: ExprId,
) -> ExprId {
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_real = embed(d, p, frac);
    let zero_c = czero_local(d, p);

    let refl_na = d.lemma(p.le_refl, &[na]);
    let a_na = cadd(d, p, a, na);
    let shifted = d.lemma(p.add_le_add, &[a, b, na, na, hab, refl_na]);
    let hn = d.lemma(p.add_neg, &[a]);
    let refl_width = d.lemma(p.equiv_refl, &[width]);
    let width_nonneg = d.lemma(
        p.le_congr,
        &[a_na, zero_c, width, width, hn, refl_width, shifted],
    );

    let rzero = d.kernel().const_(p.rat.zero, vec![]);
    let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, m]);
    let frac_nonneg = d.lemma(p.of_rat_le, &[rzero, frac, rle]);

    d.lemma(p.mul_nonneg, &[width, frac_real, width_nonneg, frac_nonneg])
}

/// From `h : Nat.le (add q q) (Nat.succ (add m m))`, derive `Nat.le q m`.
///
/// `Nat.lt_or_ge m q` splits; the `Le q m` side is the answer, and the
/// `Lt m q` side doubles `succ m <= q` on both sides
/// (`add_le_add_right`/`add_le_add_left` plus `le_trans`) to reach
/// `Le (succ (succ (add m m))) (succ (add m m))`, refuted by
/// `Nat.not_succ_le_self`. The one non-defeq step is `Nat.succ_add`, since
/// `add (succ m) (succ m)` reduces to `succ (add (succ m) m)` -- `Nat.add`
/// recurses on its RIGHT argument -- and not to `succ (succ (add m m))`.
fn nat_double_le(d: &mut IntDev<'_>, p: CRealPrelude, q: ExprId, m: ExprId, h: ExprId) -> ExprId {
    let nat_p = p.rat.int.nat;
    let target = d.le(q, m);
    let lt_ty = d.lt(m, q);
    let le_ty = d.le(q, m);
    let disj = d.lemma(nat_p.lt_or_ge, &[m, q]);
    d.or_elim(
        lt_ty,
        le_ty,
        target,
        disj,
        &|d: &mut IntDev<'_>, hlt: ExprId| -> ExprId {
            let sm = d.succ(m);
            let s1 = d.lemma(nat_p.add_le_add_right, &[sm, sm, q, hlt]);
            let s2 = d.lemma(nat_p.add_le_add_left, &[q, sm, q, hlt]);
            let ss = NatOps::add(d, sm, sm);
            let qs = NatOps::add(d, q, sm);
            let qq = NatOps::add(d, q, q);
            let t1 = d.lemma(nat_p.le_trans, &[ss, qs, qq, s1, s2]);
            let mm = NatOps::add(d, m, m);
            let smm = d.succ(mm);
            let t2 = d.lemma(nat_p.le_trans, &[ss, qq, smm, t1, h]);
            // t2 : Le (add (succ m) (succ m)) (succ (add m m))
            //    == Le (succ (add (succ m) m)) (succ (add m m))  (defeq)
            let succ_add_eq = d.lemma(nat_p.succ_add, &[m, m]);
            let add_sm_m = NatOps::add(d, sm, m);
            let rewritten = nat_rewrite_prop(d, add_sm_m, smm, succ_add_eq, t2, &|d, t| {
                let st = d.succ(t);
                d.le(st, smm)
            });
            // rewritten : Le (succ (succ (add m m))) (succ (add m m))
            let contra = d.lemma(nat_p.not_succ_le_self, &[smm]);
            let falsity = d.apply(contra, &[rewritten]);
            d.absurd(target, falsity)
        },
        &|_d: &mut IntDev<'_>, hle: ExprId| -> ExprId { hle },
    )
}

/// The body of [`near_coarse_pred`] at an explicit coarse index:
/// `And (Nat.le i (meshLevelCount j))
///      (And (le (P j i) (P level i'))
///           (le (add (P level i') (D level)) (add (P j i) (D j))))`.
///
/// The second conjunct is deliberately stated with `D level` on the LEFT
/// rather than as a bare `le (P level i') (add (P j i) (D j))`: carrying the
/// fine width makes the induction below EXACT (the accumulated displacement
/// telescopes to `D j - D level`), where the weaker form loses a summand at
/// every doubling and does not close.
fn near_coarse_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    j: ExprId,
    level: ExprId,
    fine: ExprId,
    coarse: ExprId,
) -> ExprId {
    let mlc_j = d.const_app(p.mesh_level_count, &[j]);
    let bound = d.le(coarse, mlc_j);
    let pj = level_point(d, p, a, b, j, coarse);
    let pl = level_point(d, p, a, b, level, fine);
    let lower = cle(d, p, pj, pl);
    let dl = level_delta(d, p, a, b, level);
    let dj = level_delta(d, p, a, b, j);
    let lhs = cadd(d, p, pl, dl);
    let rhs = cadd(d, p, pj, dj);
    let upper = cle(d, p, lhs, rhs);
    let inner = d.and(lower, upper);
    d.and(bound, inner)
}

/// `fun i => near_coarse_body ...` -- the `Exists` predicate.
fn near_coarse_pred(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    j: ExprId,
    level: ExprId,
    fine: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = near_coarse_body(d, p, a, b, j, level, fine, i);
    d.lam_fv(i_fv, nat, body)
}

/// `Exists.{1} Nat (near_coarse_pred ...)`.
fn near_coarse_stmt(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    j: ExprId,
    level: ExprId,
    fine: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = near_coarse_pred(d, p, a, b, j, level, fine);
    let exists_name = p.rat.int.logic.exists_;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists_const, &[nat, pred])
}

/// `Exists.intro.{1}` at [`near_coarse_pred`].
fn near_coarse_intro(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    j: ExprId,
    level: ExprId,
    fine: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = near_coarse_pred(d, p, a, b, j, level, fine);
    let intro_name = p.rat.int.logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[nat, pred, witness, proof])
}

/// One parity branch of [`declare_mesh_point_near_coarse_thm`]'s induction
/// step, at fine level `Nat.succ ll`.
///
/// `heq` is `Eq ip (add q q)` (`odd = false`) or `Eq ip (succ (add q q))`
/// (`odd = true`), `h : Nat.le ip (meshLevelCount (succ ll))`, and `ih` is the
/// induction hypothesis at level `ll`. Produces the `Exists` statement about
/// `ip` itself: the whole argument runs at the parity-normalized index and is
/// transported back along `heq` at the very end.
fn near_coarse_step_case(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    j: ExprId,
    hab: ExprId,
    ll: ExprId,
    ih: ExprId,
    ip: ExprId,
    h: ExprId,
    q: ExprId,
    odd: bool,
    heq: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let nat_p = p.rat.int.nat;
    let sll = d.succ(ll);
    let mm = d.const_app(p.mesh_level_count, &[ll]);
    let mmm = NatOps::add(d, mm, mm);
    let smmm = d.succ(mmm);
    let qq = NatOps::add(d, q, q);
    let sqq = d.succ(qq);
    let fine = if odd { sqq } else { qq };

    // hqq : Nat.le (add q q) (succ (add mm mm)), in both parities.
    let hqq = if odd {
        let shifted = nat_rewrite_prop(d, ip, sqq, heq, h, &|d, t| d.le(t, smmm));
        let peeled = d.lemma(nat_p.le_of_succ_le_succ, &[qq, mmm, shifted]);
        d.lemma(nat_p.le_succ_of_le, &[qq, mmm, peeled])
    } else {
        nat_rewrite_prop(d, ip, qq, heq, h, &|d, t| d.le(t, smmm))
    };
    let hq = nat_double_le(d, p, q, mm, hqq);

    let ihq = d.apply(ih, &[q, hq]);
    let pred_ll = near_coarse_pred(d, p, a, b, j, ll, q);
    let target_fine = near_coarse_stmt(d, p, a, b, j, sll, fine);

    let minor = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let hp_ty = near_coarse_body(d, p, a, b, j, ll, q, i);

        // Destructure the induction hypothesis's conjunction.
        let mlc_j = d.const_app(p.mesh_level_count, &[j]);
        let bound_ty = d.le(i, mlc_j);
        let pj = level_point(d, p, a, b, j, i);
        let pll = level_point(d, p, a, b, ll, q);
        let dll = level_delta(d, p, a, b, ll);
        let dj = level_delta(d, p, a, b, j);
        let lower_ty = cle(d, p, pj, pll);
        let sum_ll = cadd(d, p, pll, dll);
        let sum_j = cadd(d, p, pj, dj);
        let upper_ty = cle(d, p, sum_ll, sum_j);
        let inner_ty = d.and(lower_ty, upper_ty);
        let hi = d.and_left(bound_ty, inner_ty, hp);
        let rest = d.and_right(bound_ty, inner_ty, hp);
        let h1 = d.and_left(lower_ty, upper_ty, rest);
        let h2 = d.and_right(lower_ty, upper_ty, rest);

        // Shared geometry: the fine width, its nonnegativity, the exact
        // even-index coincidence, and the halving identity.
        let dsll = level_delta(d, p, a, b, sll);
        let mlc_sll = d.const_app(p.mesh_level_count, &[sll]);
        let dsll_nonneg = mesh_delta_nonneg(d, p, a, b, mlc_sll, hab);
        let tr = mesh_sample_transport(d, p, a, b, ll, q);
        let psll_qq = level_point(d, p, a, b, sll, qq);
        let halve = mesh_delta_halve(d, p, a, b, ll);

        // dsll <= dll, from `dsll + dsll ~ dll` and `dsll >= 0`.
        let grown = shift_le_of_nonneg_local(d, p, dsll, dsll, dsll_nonneg);
        let sum_dsll = cadd(d, p, dsll, dsll);
        let refl_dsll = d.lemma(p.equiv_refl, &[dsll]);
        let dsll_le_dll = d.lemma(
            p.le_congr,
            &[dsll, dsll, sum_dsll, dll, refl_dsll, halve, grown],
        );

        let (lower_new, upper_new, p_fine) = if odd {
            let podd = level_point(d, p, a, b, sll, sqq);
            let e1 = sample_succ_equiv(d, p, a, dsll, qq);
            let psll_qq_plus = cadd(d, p, psll_qq, dsll);
            let tr_symm = d.lemma(p.equiv_symm, &[pll, psll_qq, tr]);
            let refl_d1 = d.lemma(p.equiv_refl, &[dsll]);
            let e2 = d.lemma(p.add_congr, &[psll_qq, pll, dsll, dsll, tr_symm, refl_d1]);
            let pll_plus = cadd(d, p, pll, dsll);
            let eodd = d.lemma(p.equiv_trans, &[podd, psll_qq_plus, pll_plus, e1, e2]);

            // (A) le pj podd.
            let grow = shift_le_of_nonneg_local(d, p, pll, dsll, dsll_nonneg);
            let chain_a = d.lemma(p.le_trans, &[pj, pll, pll_plus, h1, grow]);
            let eodd_symm = d.lemma(p.equiv_symm, &[podd, pll_plus, eodd]);
            let refl_pj = d.lemma(p.equiv_refl, &[pj]);
            let lower_new = d.lemma(
                p.le_congr,
                &[pj, pj, pll_plus, podd, refl_pj, eodd_symm, chain_a],
            );

            // (B) le (add podd dsll) (add pj dj).
            let refl_d2 = d.lemma(p.equiv_refl, &[dsll]);
            let c1 = d.lemma(p.add_congr, &[podd, pll_plus, dsll, dsll, eodd, refl_d2]);
            let lhs_b = cadd(d, p, podd, dsll);
            let mid_b1 = cadd(d, p, pll_plus, dsll);
            let c2 = d.lemma(p.add_assoc, &[pll, dsll, dsll]);
            let mid_b2 = cadd(d, p, pll, sum_dsll);
            let refl_pll = d.lemma(p.equiv_refl, &[pll]);
            let c3 = d.lemma(p.add_congr, &[pll, pll, sum_dsll, dll, refl_pll, halve]);
            let k1 = d.lemma(p.equiv_trans, &[lhs_b, mid_b1, mid_b2, c1, c2]);
            let cfull = d.lemma(p.equiv_trans, &[lhs_b, mid_b2, sum_ll, k1, c3]);
            let cfull_symm = d.lemma(p.equiv_symm, &[lhs_b, sum_ll, cfull]);
            let refl_rhs = d.lemma(p.equiv_refl, &[sum_j]);
            let upper_new = d.lemma(
                p.le_congr,
                &[sum_ll, lhs_b, sum_j, sum_j, cfull_symm, refl_rhs, h2],
            );
            (lower_new, upper_new, podd)
        } else {
            // (A) le pj (P sll (add q q)).
            let refl_pj = d.lemma(p.equiv_refl, &[pj]);
            let lower_new = d.lemma(p.le_congr, &[pj, pj, pll, psll_qq, refl_pj, tr, h1]);

            // (B) le (add (P sll (add q q)) dsll) (add pj dj).
            let tr_symm = d.lemma(p.equiv_symm, &[pll, psll_qq, tr]);
            let le_pq = d.lemma(p.le_of_equiv, &[psll_qq, pll, tr_symm]);
            let step_b = d.lemma(p.add_le_add, &[psll_qq, pll, dsll, dll, le_pq, dsll_le_dll]);
            let lhs_b = cadd(d, p, psll_qq, dsll);
            let upper_new = d.lemma(p.le_trans, &[lhs_b, sum_ll, sum_j, step_b, h2]);
            (lower_new, upper_new, psll_qq)
        };

        let lower_ty_new = cle(d, p, pj, p_fine);
        let lhs_new = cadd(d, p, p_fine, dsll);
        let upper_ty_new = cle(d, p, lhs_new, sum_j);
        let inner_new = and_intro(d, p, lower_ty_new, upper_ty_new, lower_new, upper_new);
        let inner_ty_new = d.and(lower_ty_new, upper_ty_new);
        let whole = and_intro(d, p, bound_ty, inner_ty_new, hi, inner_new);
        let witnessed = near_coarse_intro(d, p, a, b, j, sll, fine, i, whole);

        let inner_lam = d.lam_fv(hp_fv, hp_ty, witnessed);
        d.lam_fv(i_fv, nat, inner_lam)
    };

    let at_fine = exists_elim(d, pred_ll, target_fine, ihq, minor);
    let heq_symm = NatOps::symm(d, ip, fine, heq);
    nat_rewrite_prop(d, fine, ip, heq_symm, at_fine, &|d, t| {
        near_coarse_stmt(d, p, a, b, j, sll, t)
    })
}

/// `CReal.meshPoint_near_coarse : ∀ a b j, le a b → ∀ d i',
/// Nat.le i' (meshLevelCount (Nat.add j d)) →
/// ∃ i, Nat.le i (meshLevelCount j) ∧
///      le (P j i) (P (add j d) i') ∧
///      le (add (P (add j d) i') (D (add j d))) (add (P j i) (D j))`
///
/// where `P L i := meshSamplePoint a (meshDelta a b (meshLevelCount L)) i` and
/// `D L := meshDelta a b (meshLevelCount L)` -- **the multi-level
/// nearest-mesh-point lemma**, and the piece rung 6's gap bound needs that
/// nothing in the tree had. At refinement depth 1 this is
/// [`mesh_sample_transport`]'s exact even-index coincidence; at ARBITRARY
/// depth it is a genuine "which coarse cell contains this fine point"
/// statement, which the module documentation's "Rung 6 re-verified" section
/// identifies as the real obstruction.
///
/// **It needs no `Nat` division function, and that is the point.** The
/// obvious route computes the coarse index as `i' / 2^d` and instantiates
/// [`CRealPrelude::max_range_transport`]; this one never names the index at
/// all. The conclusion is `Prop`-valued, so `Exists.rec` applies (kernel fact
/// 2 constrains only `Type`-valued conclusions), and the witness may therefore
/// be produced by an existential that the induction step re-eliminates. The
/// step's own parity split is [`NatPrelude::even_or_odd`](crate::NatPrelude::even_or_odd)'s COMPUTED half
/// `Nat.div i' 2` -- a projection, never a search.
///
/// The induction is on the depth `d`, with `a`, `b`, `j` and `hab` fixed, and
/// the invariant carries the FINE width on the left of the upper bound (see
/// [`near_coarse_body`]): that makes each step exact rather than
/// slack-accumulating. Even step: the fine point IS the coarse point
/// ([`mesh_sample_transport`]) and `D (succ ll) <= D ll` closes the upper
/// half. Odd step: the fine point is the even one plus exactly one fine width
/// ([`sample_succ_equiv`]), and the two fine widths fuse back to one coarse
/// width by [`mesh_delta_halve`] -- the upper bound is then EQUALITY, not an
/// estimate.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_mesh_point_near_coarse_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let nat_p = p.rat.int.nat;

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let dd_fv = d.fresh_fvar();
    let dd = d.kernel().fvar(dd_fv);

    let motive = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let level = NatOps::add(d, j, k);
        let mlc = d.const_app(p.mesh_level_count, &[level]);
        let ip_fv = d.fresh_fvar();
        let ip = d.kernel().fvar(ip_fv);
        let h_ty = d.le(ip, mlc);
        let concl = near_coarse_stmt(d, p, a, b, j, level, ip);
        let inner = d.arrow(h_ty, concl);
        d.pi_fv(ip_fv, nat, inner)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero_n = d.zero();
        let level = NatOps::add(d, j, zero_n);
        let mlc = d.const_app(p.mesh_level_count, &[level]);
        let ip_fv = d.fresh_fvar();
        let ip = d.kernel().fvar(ip_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let h_ty = d.le(ip, mlc);

        let mlc_j = d.const_app(p.mesh_level_count, &[j]);
        let bound_ty = d.le(ip, mlc_j);
        let pj = level_point(d, p, a, b, j, ip);
        let pl = level_point(d, p, a, b, level, ip);
        let dj = level_delta(d, p, a, b, j);
        let dl = level_delta(d, p, a, b, level);
        let lower_ty = cle(d, p, pj, pl);
        let lhs = cadd(d, p, pl, dl);
        let rhs = cadd(d, p, pj, dj);
        let upper_ty = cle(d, p, lhs, rhs);
        let lower = d.lemma(p.le_refl, &[pj]);
        let upper = d.lemma(p.le_refl, &[rhs]);
        let inner = and_intro(d, p, lower_ty, upper_ty, lower, upper);
        let inner_ty = d.and(lower_ty, upper_ty);
        let whole = and_intro(d, p, bound_ty, inner_ty, h, inner);
        let witnessed = near_coarse_intro(d, p, a, b, j, level, ip, ip, whole);
        let inner_lam = d.lam_fv(h_fv, h_ty, witnessed);
        d.lam_fv(ip_fv, nat, inner_lam)
    };

    let step = |d: &mut IntDev<'_>, k: ExprId, ih: ExprId| -> ExprId {
        let ll = NatOps::add(d, j, k);
        let sll = d.succ(ll);
        let mlc_sll = d.const_app(p.mesh_level_count, &[sll]);
        let ip_fv = d.fresh_fvar();
        let ip = d.kernel().fvar(ip_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let h_ty = d.le(ip, mlc_sll);

        let two = d.num(2);
        let q = NatOps::div(d, ip, two);
        let qq = NatOps::add(d, q, q);
        let sqq = d.succ(qq);
        let even_ty = d.eq(ip, qq);
        let odd_ty = d.eq(ip, sqq);
        let target = near_coarse_stmt(d, p, a, b, j, sll, ip);
        let par = d.lemma(nat_p.even_or_odd, &[ip]);

        let body = d.or_elim(
            even_ty,
            odd_ty,
            target,
            par,
            &|d: &mut IntDev<'_>, heven: ExprId| -> ExprId {
                near_coarse_step_case(d, p, a, b, j, hab, ll, ih, ip, h, q, false, heven)
            },
            &|d: &mut IntDev<'_>, hodd: ExprId| -> ExprId {
                near_coarse_step_case(d, p, a, b, j, hab, ll, ih, ip, h, q, true, hodd)
            },
        );
        let inner_lam = d.lam_fv(h_fv, h_ty, body);
        d.lam_fv(ip_fv, nat, inner_lam)
    };

    let proof = d.induct(&motive, &base, &step, dd);
    let concl = motive(d, dd);

    let ty = {
        let over_dd = d.pi_fv(dd_fv, nat, concl);
        let after_hab = d.arrow(hab_ty, over_dd);
        let over_j = d.pi_fv(j_fv, nat, after_hab);
        let over_b = d.pi_fv(b_fv, carrier, over_j);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let over_dd = d.lam_fv(dd_fv, nat, proof);
        let after_hab = d.lam_fv(hab_fv, hab_ty, over_dd);
        let over_j = d.lam_fv(j_fv, nat, after_hab);
        let over_b = d.lam_fv(b_fv, carrier, over_j);
        d.lam_fv(a_fv, carrier, over_b)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_point_near_coarse,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.meshPoint_near_coarse` alone (a one-declaration `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_point_near_coarse(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_point_near_coarse_thm(d, p)
}

/// `CReal.maxRange_le_add_of_exists : ∀ f g n n' eps,
/// (∀ i, Nat.le i n → ∃ i', Nat.le i' n' ∧ le (f i) (add (g i') eps)) →
/// le (maxRange f n) (add (maxRange g n') eps)` -- the APPROXIMATE,
/// EXISTENTIAL-witnessed form of [`CRealPrelude::max_range_transport`].
///
/// Two changes from `maxRange_transport`, and both matter for rung 6:
///
/// - the per-index relation is `le (f i) (add (g (e i)) eps)` rather than
///   `Equiv (f i) (g (e i))`, so it survives a bound that is not exact; and
/// - the coarse index is an `Exists` WITNESS rather than a supplied function
///   `e : Nat → Nat`.
///
/// The second is what removes the need for a `Nat` division function. Bounding
/// a fine mesh maximum by a coarse one wants `e i := i / 2^d`, and this kernel
/// does have `Nat.div` -- but the conclusion here is `Prop`, so `Exists.rec`
/// applies (kernel fact 2 constrains only `Type`-valued conclusions) and
/// [`CRealPrelude::mesh_point_near_coarse`]'s existential plugs straight in
/// with no quotient/remainder algebra at all.
///
/// Same auxiliary induction as `maxRange_transport` (motive `fun k => Nat.le k
/// n → le (maxRange f k) (add (maxRange g n') eps)`, discharged at `k := n`
/// with `Nat.le_refl n`); each case eliminates the existential and closes with
/// [`CRealPrelude::max_range_ub`] padded by `eps` through
/// [`CRealPrelude::add_le_add`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_max_range_le_add_of_exists_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_p = p.rat.int.nat;
    let logic = p.rat.int.logic;
    let one_level = d.level_one();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let np_fv = d.fresh_fvar();
    let np = d.kernel().fvar(np_fv);
    let eps_fv = d.fresh_fvar();
    let eps = d.kernel().fvar(eps_fv);

    // `fun i' => And (Nat.le i' n') (le (f i) (add (g i') eps))`.
    let witness_pred = |d: &mut IntDev<'_>, i: ExprId| -> ExprId {
        let ip_fv = d.fresh_fvar();
        let ip = d.kernel().fvar(ip_fv);
        let bound = d.le(ip, np);
        let gi = d.apply(g, &[ip]);
        let padded = cadd(d, p, gi, eps);
        let fi = d.apply(f, &[i]);
        let est = cle(d, p, fi, padded);
        let body = d.and(bound, est);
        d.lam_fv(ip_fv, nat, body)
    };

    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.le(i, n);
        let pred = witness_pred(d, i);
        let exists_const = d.kernel().const_(logic.exists_, vec![one_level]);
        let stmt = d.apply(exists_const, &[nat, pred]);
        let inner = d.arrow(hi_ty, stmt);
        d.pi_fv(i_fv, nat, inner)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    // `le (f i) (add (maxRange g n') eps)`, given `i` and `hi : Nat.le i n`.
    let pointwise = |d: &mut IntDev<'_>, i: ExprId, hi: ExprId, target: ExprId| -> ExprId {
        let pred = witness_pred(d, i);
        let ex = d.apply(hyp, &[i, hi]);
        let minor = {
            let ip_fv = d.fresh_fvar();
            let ip = d.kernel().fvar(ip_fv);
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            let bound_ty = d.le(ip, np);
            let gi = d.apply(g, &[ip]);
            let padded = cadd(d, p, gi, eps);
            let fi = d.apply(f, &[i]);
            let est_ty = cle(d, p, fi, padded);
            let hp_ty = d.and(bound_ty, est_ty);
            let hb = d.and_left(bound_ty, est_ty, hp);
            let hle = d.and_right(bound_ty, est_ty, hp);

            let ub = d.lemma(p.max_range_ub, &[g, np, ip, hb]);
            let mr = d.const_app(p.max_range, &[g, np]);
            let refl_eps = d.lemma(p.le_refl, &[eps]);
            let grown = d.lemma(p.add_le_add, &[gi, mr, eps, eps, ub, refl_eps]);
            let goal_rhs = cadd(d, p, mr, eps);
            let chained = d.lemma(p.le_trans, &[fi, padded, goal_rhs, hle, grown]);
            let inner = d.lam_fv(hp_fv, hp_ty, chained);
            d.lam_fv(ip_fv, nat, inner)
        };
        exists_elim(d, pred, target, ex, minor)
    };

    let motive = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let h_ty = d.le(k, n);
        let mrk = d.const_app(p.max_range, &[f, k]);
        let mr = d.const_app(p.max_range, &[g, np]);
        let rhs = cadd(d, p, mr, eps);
        let concl = cle(d, p, mrk, rhs);
        d.arrow(h_ty, concl)
    };

    let proof = d.induct(
        &motive,
        &|d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            let h0_fv = d.fresh_fvar();
            let h0 = d.kernel().fvar(h0_fv);
            let h0_ty = d.le(zero_n, n);
            let mr0 = d.const_app(p.max_range, &[f, zero_n]);
            let mr = d.const_app(p.max_range, &[g, np]);
            let rhs = cadd(d, p, mr, eps);
            let target = cle(d, p, mr0, rhs);
            let result = pointwise(d, zero_n, h0, target);
            d.lam_fv(h0_fv, h0_ty, result)
        },
        &|d: &mut IntDev<'_>, jj: ExprId, ih: ExprId| -> ExprId {
            let sj = d.succ(jj);
            let hsj_fv = d.fresh_fvar();
            let hsj = d.kernel().fvar(hsj_fv);
            let hsj_ty = d.le(sj, n);

            let le_succ_j = d.lemma(nat_p.le_succ, &[jj]);
            let hj = d.lemma(nat_p.le_trans, &[jj, sj, n, le_succ_j, hsj]);
            let ih_hj = d.apply(ih, &[hj]);

            let mr = d.const_app(p.max_range, &[g, np]);
            let rhs = cadd(d, p, mr, eps);
            let fsj = d.apply(f, &[sj]);
            let target = cle(d, p, fsj, rhs);
            let head = pointwise(d, sj, hsj, target);

            let mrj = d.const_app(p.max_range, &[f, jj]);
            let combine = d.lemma(p.max_le, &[mrj, fsj, rhs, ih_hj, head]);
            d.lam_fv(hsj_fv, hsj_ty, combine)
        },
        n,
    );

    let le_refl_n = d.lemma(nat_p.le_refl, &[n]);
    let value_body = d.apply(proof, &[le_refl_n]);

    let mrn = d.const_app(p.max_range, &[f, n]);
    let mr_final = d.const_app(p.max_range, &[g, np]);
    let rhs_final = cadd(d, p, mr_final, eps);
    let conclusion = cle(d, p, mrn, rhs_final);

    let ty = {
        let out = d.arrow(hyp_ty, conclusion);
        let out = d.pi_fv(eps_fv, carrier, out);
        let out = d.pi_fv(np_fv, nat, out);
        let out = d.pi_fv(n_fv, nat, out);
        let out = d.pi_fv(g_fv, fn_ty, out);
        d.pi_fv(f_fv, fn_ty, out)
    };
    let value = {
        let out = d.lam_fv(hyp_fv, hyp_ty, value_body);
        let out = d.lam_fv(eps_fv, carrier, out);
        let out = d.lam_fv(np_fv, nat, out);
        let out = d.lam_fv(n_fv, nat, out);
        let out = d.lam_fv(g_fv, fn_ty, out);
        d.lam_fv(f_fv, fn_ty, out)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_range_le_add_of_exists,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.maxRange_le_add_of_exists` alone (a one-declaration
/// `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_max_range_le_add_of_exists(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_max_range_le_add_of_exists_thm(d, p)
}

/// `CReal.meshMax_le_add_of_step_close : ∀ F a b j d eps, le a b →
/// (∀ x y, le a x → le x b → le a y → le y b → le x y →
///         le y (add x (meshDelta a b (meshLevelCount j))) →
///         le (F y) (add (F x) eps)) →
/// le (meshMax F a b (Nat.add j d)) (add (meshMax F a b j) eps)`
///
/// **Rung 6's gap bound, with the accuracy schedule factored out.** This is
/// the statement the telescope consumes, and it holds at ARBITRARY refinement
/// depth `d` -- not just one doubling. Everything geometric is discharged
/// here; what remains for a `supOn` assembly is purely to instantiate
/// `hclose` from [`CRealPrelude::uc_spec`] at the accuracy
/// [`CRealPrelude::exp_of_modulus`] selects, which is arithmetic about the
/// modulus and involves no mesh geometry at all.
///
/// Note what the hypothesis is NOT: it is not two-sided, and it is not about
/// `abs`. `hclose` only bounds how much `F` can RISE across a rightward step
/// of at most one level-`j` cell, which is all a MAXIMUM needs -- the other
/// direction is [`CRealPrelude::mesh_max_mono`], already landed and free.
///
/// Route: [`CRealPrelude::mesh_point_near_coarse`] supplies, for each fine
/// index, a coarse index whose sample point sits just below the fine one and
/// within one coarse width of it (conjunct (B) is stated with the FINE width
/// on the left, so `shift_le_of_nonneg_local` plus `le_trans` turns it into
/// the plain `le y (add x (D j))` that `hclose` wants);
/// [`CRealPrelude::riemann_sample_in_bounds`] places both points in `[a, b]`;
/// and [`CRealPrelude::max_range_le_add_of_exists`] lifts the pointwise
/// estimate to the two mesh maxima. `meshMax` unfolds to `maxRange` on the
/// sampler by delta, exactly as in [`declare_mesh_max_step_le_thm`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_mesh_max_le_add_of_step_close_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;
    let logic = p.rat.int.logic;
    let one_level = d.level_one();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let dd_fv = d.fresh_fvar();
    let dd = d.kernel().fvar(dd_fv);
    let eps_fv = d.fresh_fvar();
    let eps = d.kernel().fvar(eps_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let level = NatOps::add(d, j, dd);
    let mlc_j = d.const_app(p.mesh_level_count, &[j]);
    let mlc_l = d.const_app(p.mesh_level_count, &[level]);
    let dj = level_delta(d, p, a, b, j);

    // hclose : ∀ x y, le a x → le x b → le a y → le y b → le x y →
    //          le y (add x (D j)) → le (F y) (add (F x) eps).
    let hclose_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax = cle(d, p, a, x);
        let hxb = cle(d, p, x, b);
        let hay = cle(d, p, a, y);
        let hyb = cle(d, p, y, b);
        let hxy = cle(d, p, x, y);
        let shifted = cadd(d, p, x, dj);
        let hstep = cle(d, p, y, shifted);
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let padded = cadd(d, p, fx, eps);
        let concl = cle(d, p, fy, padded);
        let out = d.arrow(hstep, concl);
        let out = d.arrow(hxy, out);
        let out = d.arrow(hyb, out);
        let out = d.arrow(hay, out);
        let out = d.arrow(hxb, out);
        let out = d.arrow(hax, out);
        let over_y = d.pi_fv(y_fv, carrier, out);
        d.pi_fv(x_fv, carrier, over_y)
    };
    let hclose_fv = d.fresh_fvar();
    let hclose = d.kernel().fvar(hclose_fv);

    let fine_sampler = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = level_point(d, p, a, b, level, i);
        let fx = d.apply(f, &[sp]);
        d.lam_fv(i_fv, nat, fx)
    };
    let coarse_sampler = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = level_point(d, p, a, b, j, i);
        let fx = d.apply(f, &[sp]);
        d.lam_fv(i_fv, nat, fx)
    };

    // hyp : ∀ i, Nat.le i (mlc level) →
    //       ∃ i', Nat.le i' (mlc j) ∧ le (F (P level i)) (add (F (P j i')) eps).
    let hyp = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.le(i, mlc_l);

        let y = level_point(d, p, a, b, level, i);
        let fy = d.apply(f, &[y]);

        // The target `Exists` in the shape `max_range_le_add_of_exists` wants.
        let goal_pred = {
            let ip_fv = d.fresh_fvar();
            let ip = d.kernel().fvar(ip_fv);
            let bound = d.le(ip, mlc_j);
            let x = level_point(d, p, a, b, j, ip);
            let fx = d.apply(f, &[x]);
            let padded = cadd(d, p, fx, eps);
            let est = cle(d, p, fy, padded);
            let body = d.and(bound, est);
            d.lam_fv(ip_fv, nat, body)
        };
        let exists_const = d.kernel().const_(logic.exists_, vec![one_level]);
        let goal = d.apply(exists_const, &[nat, goal_pred]);

        let near = d.const_app(p.mesh_point_near_coarse, &[a, b, j, hab, dd, i, hi]);
        let near_pred = near_coarse_pred(d, p, a, b, j, level, i);

        let minor = {
            let ip_fv = d.fresh_fvar();
            let ip = d.kernel().fvar(ip_fv);
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            let hp_ty = near_coarse_body(d, p, a, b, j, level, i, ip);

            let bound_ty = d.le(ip, mlc_j);
            let x = level_point(d, p, a, b, j, ip);
            let dl = level_delta(d, p, a, b, level);
            let lower_ty = cle(d, p, x, y);
            let sum_l = cadd(d, p, y, dl);
            let sum_j = cadd(d, p, x, dj);
            let upper_ty = cle(d, p, sum_l, sum_j);
            let inner_ty = d.and(lower_ty, upper_ty);
            let hi_bound = d.and_left(bound_ty, inner_ty, hp);
            let rest = d.and_right(bound_ty, inner_ty, hp);
            let h_lower = d.and_left(lower_ty, upper_ty, rest);
            let h_upper = d.and_right(lower_ty, upper_ty, rest);

            // Both sample points lie in [a, b].
            let hlt_ip = d.lemma(nat_p.lt_succ_of_le, &[ip, mlc_j, hi_bound]);
            let and_x = d.const_app(p.riemann_sample_in_bounds, &[a, b, mlc_j, ip, hab, hlt_ip]);
            let a_le_x = cle(d, p, a, x);
            let x_le_b = cle(d, p, x, b);
            let hax = d.const_app(logic.and_left, &[a_le_x, x_le_b, and_x]);
            let hxb = d.const_app(logic.and_right, &[a_le_x, x_le_b, and_x]);

            let hlt_i = d.lemma(nat_p.lt_succ_of_le, &[i, mlc_l, hi]);
            let and_y = d.const_app(p.riemann_sample_in_bounds, &[a, b, mlc_l, i, hab, hlt_i]);
            let a_le_y = cle(d, p, a, y);
            let y_le_b = cle(d, p, y, b);
            let hay = d.const_app(logic.and_left, &[a_le_y, y_le_b, and_y]);
            let hyb = d.const_app(logic.and_right, &[a_le_y, y_le_b, and_y]);

            // `le y (add x (D j))`, dropping the fine width the invariant carries.
            let mlc_l_term = d.const_app(p.mesh_level_count, &[level]);
            let dl_nonneg = mesh_delta_nonneg(d, p, a, b, mlc_l_term, hab);
            let y_grown = shift_le_of_nonneg_local(d, p, y, dl, dl_nonneg);
            let hstep = d.lemma(p.le_trans, &[y, sum_l, sum_j, y_grown, h_upper]);

            let est = d.apply(hclose, &[x, y, hax, hxb, hay, hyb, h_lower, hstep]);
            let whole = {
                let fx = d.apply(f, &[x]);
                let padded = cadd(d, p, fx, eps);
                let est_ty = cle(d, p, fy, padded);
                and_intro(d, p, bound_ty, est_ty, hi_bound, est)
            };
            let intro = d.kernel().const_(logic.exists_intro, vec![one_level]);
            let witnessed = d.apply(intro, &[nat, goal_pred, ip, whole]);
            let inner = d.lam_fv(hp_fv, hp_ty, witnessed);
            d.lam_fv(ip_fv, nat, inner)
        };

        let elim = exists_elim(d, near_pred, goal, near, minor);
        let inner = d.lam_fv(hi_fv, hi_ty, elim);
        d.lam_fv(i_fv, nat, inner)
    };

    let applied = d.const_app(
        p.max_range_le_add_of_exists,
        &[fine_sampler, coarse_sampler, mlc_l, mlc_j, eps, hyp],
    );

    let mesh_l = d.const_app(p.mesh_max, &[f, a, b, level]);
    let mesh_j = d.const_app(p.mesh_max, &[f, a, b, j]);
    let rhs = cadd(d, p, mesh_j, eps);
    let conclusion = cle(d, p, mesh_l, rhs);

    let ty = {
        let out = d.arrow(hclose_ty, conclusion);
        let out = d.arrow(hab_ty, out);
        let out = d.pi_fv(eps_fv, carrier, out);
        let out = d.pi_fv(dd_fv, nat, out);
        let out = d.pi_fv(j_fv, nat, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(hclose_fv, hclose_ty, applied);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(eps_fv, carrier, out);
        let out = d.lam_fv(dd_fv, nat, out);
        let out = d.lam_fv(j_fv, nat, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_max_le_add_of_step_close,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.meshMax_le_add_of_step_close` alone (a one-declaration
/// `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_max_le_add_of_step_close(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_max_le_add_of_step_close_thm(d, p)
}

// ---------------------------------------------------------------------------
// `CReal.meshLevelCount_pow` -- bridges the additive doubling schedule
// (`meshLevelCount`) to `Nat.pow`, needed to route `Nat.lt_pow_size`'s
// power-of-two dominance bound back into a concrete mesh LEVEL via
// `Nat.size`. See the module documentation's "Rung 6, the telescope" and
// "What rung 6 still owes" sections.
// ---------------------------------------------------------------------------

/// `CReal.meshLevelCount_pow : ∀ j,
/// Eq Nat (Nat.succ (meshLevelCount j)) (Nat.pow 2 j)` -- `meshLevelCount`'s
/// own doc already states the informal fact (`meshLevelCount j = 2^j - 1`);
/// this is the formal, subtraction-free restatement (`+1` on the LEFT
/// instead), proved by induction on `j` via [`NatOps::induct`].
///
/// Base case: `meshLevelCount_zero` plus `Nat.pow_zero` (both give `1`
/// directly). Step case: `meshLevelCount_succ` gives `meshLevelCount (succ
/// j) + 1 = (mlc j + mlc j) + 2`; `Nat.succ_add`/`Nat.add_succ` re-associate
/// that to `(mlc j + 1) + (mlc j + 1)`; the IH rewrites `mlc j + 1` to `pow 2
/// j`; and `Nat.mul_succ`/`Nat.mul_one` fold `(pow 2 j) + (pow 2 j)` into
/// `(pow 2 j) * 2`, which is exactly `Nat.pow_succ`'s RHS at base `2`.
fn declare_mesh_level_count_pow_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_p = p.rat.int.nat;
    let one = d.level_one();
    let logic = p.rat.int.logic;

    let two_nat = d.num(2);
    let one_nat = d.num(1);

    let motive = |d: &mut IntDev<'_>, j: ExprId| -> ExprId {
        let mlc = d.const_app(p.mesh_level_count, &[j]);
        let lhs = d.succ(mlc);
        let rhs = d.const_app(nat_p.pow, &[two_nat, j]);
        let eq = d.kernel().const_(logic.eq, vec![one]);
        d.apply(eq, &[nat, lhs, rhs])
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero_n = d.zero();
        let mlc0 = d.const_app(p.mesh_level_count, &[zero_n]);
        let succ_mlc0 = d.succ(mlc0);
        let succ0 = d.succ(zero_n);
        let pow2_0 = d.const_app(nat_p.pow, &[two_nat, zero_n]);

        let mlc0_eq = d.lemma(p.mesh_level_count_zero, &[]); // Eq(mlc0, zero_n)
        let congr_succ = d.congr(mlc0, zero_n, mlc0_eq, &|d, t| d.succ(t)); // Eq(succ_mlc0, succ0)
        let pow0_eq = d.lemma(nat_p.pow_zero, &[two_nat]); // Eq(pow2_0, succ0)
        let symm_pow0 = d.symm(pow2_0, succ0, pow0_eq); // Eq(succ0, pow2_0)
        d.trans(succ_mlc0, succ0, pow2_0, congr_succ, symm_pow0)
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let sj = d.succ(j);
        let mlc_j = d.const_app(p.mesh_level_count, &[j]);
        let succ_mlc_j = d.succ(mlc_j);
        let mlc_sj = d.const_app(p.mesh_level_count, &[sj]);
        let succ_mlc_sj = d.succ(mlc_sj);
        let pow_sj = d.const_app(nat_p.pow, &[two_nat, sj]);
        let pow_j = d.const_app(nat_p.pow, &[two_nat, j]);
        let doubled = d.add(mlc_j, mlc_j);
        let succ_doubled = d.succ(doubled);

        // LHS_EQ : Eq(succ_mlc_sj, add(succ_mlc_j)(succ_mlc_j))
        let mlc_succ_eq = d.lemma(p.mesh_level_count_succ, &[j]); // Eq(mlc_sj, succ_doubled)
        let succ_succ_eq = d.congr(mlc_sj, succ_doubled, mlc_succ_eq, &|d, t| d.succ(t));
        // Eq(succ_mlc_sj, succ(succ_doubled))

        let add_succ_eq = d.lemma(nat_p.add_succ, &[succ_mlc_j, mlc_j]);
        // Eq(add(succ_mlc_j)(succ_mlc_j), succ(add(succ_mlc_j)(mlc_j)))
        let succ_add_eq = d.lemma(nat_p.succ_add, &[mlc_j, mlc_j]);
        // Eq(add(succ_mlc_j)(mlc_j), succ_doubled)
        let inner = d.add(succ_mlc_j, mlc_j);
        let congr_succ_add = d.congr(inner, succ_doubled, succ_add_eq, &|d, t| d.succ(t));
        // Eq(succ(inner), succ(succ_doubled))
        let sm_sm = d.add(succ_mlc_j, succ_mlc_j);
        let succ_inner = d.succ(inner);
        let succ_succ_doubled = d.succ(succ_doubled);
        let chain_a = d.trans(
            sm_sm,
            succ_inner,
            succ_succ_doubled,
            add_succ_eq,
            congr_succ_add,
        );
        // Eq(sm_sm, succ_succ_doubled)
        let symm_chain_a = d.symm(sm_sm, succ_succ_doubled, chain_a);
        let lhs_eq = d.trans(
            succ_mlc_sj,
            succ_succ_doubled,
            sm_sm,
            succ_succ_eq,
            symm_chain_a,
        );
        // Eq(succ_mlc_sj, sm_sm)

        // pow_sj_eq_smsm : Eq(pow_sj, sm_sm)
        let mul_one_eq = d.lemma(nat_p.mul_one, &[succ_mlc_j]); // Eq(mul(succ_mlc_j)(succ zero), succ_mlc_j)
        let mul_sm_1 = d.mul(succ_mlc_j, one_nat);
        let mul_succ_eq = d.lemma(nat_p.mul_succ, &[succ_mlc_j, one_nat]);
        // Eq(mul(succ_mlc_j)(succ one_nat), add(mul_sm_1)(succ_mlc_j))
        let add_mulsm1_sm = d.add(mul_sm_1, succ_mlc_j);
        let congr_add_mulone = d.congr(mul_sm_1, succ_mlc_j, mul_one_eq, &|d, t| {
            d.add(t, succ_mlc_j)
        });
        // Eq(add_mulsm1_sm, sm_sm)
        let two_v = d.succ(one_nat);
        let mul_smj_2 = d.mul(succ_mlc_j, two_v);
        let mul_succ1_prime = d.trans(
            mul_smj_2,
            add_mulsm1_sm,
            sm_sm,
            mul_succ_eq,
            congr_add_mulone,
        );
        // Eq(mul_smj_2, sm_sm)

        let pow_succ_eq = d.lemma(nat_p.pow_succ, &[two_nat, j]); // Eq(pow_sj, mul(pow_j)(two_nat))
        let ih_symm = d.symm(succ_mlc_j, pow_j, ih); // Eq(pow_j, succ_mlc_j)
        let mul_powj_2 = d.mul(pow_j, two_nat);
        let congr_mul_ih = d.congr(pow_j, succ_mlc_j, ih_symm, &|d, t| d.mul(t, two_nat));
        // Eq(mul_powj_2, mul(succ_mlc_j)(two_nat)) -- note two_nat and two_v must be the same ExprId
        let pow_sj_eq_mul = d.trans(pow_sj, mul_powj_2, mul_smj_2, pow_succ_eq, congr_mul_ih);
        // Eq(pow_sj, mul_smj_2)
        let pow_sj_eq_smsm = d.trans(pow_sj, mul_smj_2, sm_sm, pow_sj_eq_mul, mul_succ1_prime);
        // Eq(pow_sj, sm_sm)

        let symm_pow_sj_eq_smsm = d.symm(pow_sj, sm_sm, pow_sj_eq_smsm);
        d.trans(succ_mlc_sj, sm_sm, pow_sj, lhs_eq, symm_pow_sj_eq_smsm)
    };

    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let value = d.induct(&motive, &base, &step, j);
    let ty = {
        let body = motive(d, j);
        d.pi_fv(j_fv, nat, body)
    };
    let value = d.lam_fv(j_fv, nat, value);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_level_count_pow,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.meshLevelCount_pow` alone (a one-declaration `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_level_count_pow(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_level_count_pow_thm(d, p)
}

// ---------------------------------------------------------------------------
// Rung 6c: the ACCURACY-SCHEDULE ARITHMETIC.
//
// `mesh_max_le_add_of_step_close` (rung 6) discharges every piece of mesh
// GEOMETRY and leaves exactly one obligation behind: instantiate its `hclose`
// hypothesis from `UniformlyContinuousOn.spec`. That instantiation needs the
// level-`j` mesh width `Δⱼ := (b − a)·natDivSucc(1, meshLevelCount j)` bounded
// by the rational `natDivSucc 1 outer` the spec consumes, where `outer` is the
// modulus applied at the requested accuracy.
//
// The Archimedean half of that is NOT new work: `CReal.mesh_le_of_ge`
// (`creal/integral.rs`) already states exactly
//
//     le a b -> Nat.le ((succ (bound (b − a)))·outer + bound (b − a)) m
//       -> le (mul (b − a) (ofRat (natDivSucc 1 m))) (ofRat (natDivSucc 1 outer))
//
// and its left-hand side is SYNTACTICALLY this file's `mesh_delta a b m`. It
// reads the threshold straight off `CReal.bound` (a total computable
// projection), never off `CReal.archimedean`'s `Exists` -- which is what keeps
// the whole route clear of kernel fact 1.
//
// So what this section owes is purely `Nat`: at which LEVEL `j` does
// `meshLevelCount j` reach that threshold? Since `succ (meshLevelCount j) =
// 2^j` (`mesh_level_count_pow`) the question is `2^j >= (c+1)·(outer+1)`, and
// `Nat.lt_pow_size` answers it additively -- `size c` and `size outer` each
// cover one factor, and `pow_add` turns their SUM in the exponent into the
// PRODUCT of the two bounds. No `Nat.div`, no search, and the schedule stays
// additive, matching `trueExpOfModulus`'s own accumulator.
// ---------------------------------------------------------------------------

/// `Nat.le (pow 2 i) (pow 2 j)` from `h : Nat.le i j`.
///
/// This kernel has [`NatPrelude::pow_lt_pow_succ`](crate::NatPrelude::pow_lt_pow_succ)
/// (strict, one successor step) and
/// [`NatPrelude::pow_lt_pow_of_lt`](crate::NatPrelude::pow_lt_pow_of_lt)
/// (strict, across a gap) but no NON-strict monotonicity of `pow` in its
/// exponent, and the non-strict form is what a `Nat.le` hypothesis hands you.
/// Composed here through `Nat.le`'s own recursor rather than by case-splitting
/// `lt_or_eq_of_le`, which is `series.rs`'s [`declare_mono_of_le_succ`] shape
/// one type down: a `Prop`-into-`Prop` elimination that never touches
/// `Exists.rec`'s data restriction.
///
/// [`declare_mono_of_le_succ`]: super::CRealPrelude::mono_of_le_succ
fn pow_two_mono(d: &mut IntDev<'_>, p: CRealPrelude, i: ExprId, j: ExprId, h: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let nat_p = p.rat.int.nat;
    let two = d.num(2);
    let pow_i = d.const_app(nat_p.pow, &[two, i]);

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hx_fv = d.fresh_fvar();
        let hx_ty = d.le(i, x);
        let pow_x = d.const_app(nat_p.pow, &[two, x]);
        let body = d.le(pow_i, pow_x);
        let inner = d.lam_fv(hx_fv, hx_ty, body);
        d.lam_fv(x_fv, nat, inner)
    };
    let minor_refl = d.lemma(nat_p.le_refl, &[pow_i]);
    let minor_step = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hx_fv = d.fresh_fvar();
        let hx_ty = d.le(i, x);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let pow_x = d.const_app(nat_p.pow, &[two, x]);
        let sx = d.succ(x);
        let pow_sx = d.const_app(nat_p.pow, &[two, sx]);
        let ih_ty = d.le(pow_i, pow_x);

        // `Nat.lt (succ zero) 2` is `Nat.le 2 2` after `Nat.lt`'s own unfold.
        let h_two = d.lemma(nat_p.le_refl, &[two]);
        let strict = d.lemma(nat_p.pow_lt_pow_succ, &[two, x, h_two]);
        let succ_pow_x = d.succ(pow_x);
        let step_le = d.lemma(nat_p.le_succ, &[pow_x]);
        let adjacent = d.lemma(
            nat_p.le_trans,
            &[pow_x, succ_pow_x, pow_sx, step_le, strict],
        );
        let body = d.lemma(nat_p.le_trans, &[pow_i, pow_x, pow_sx, ih, adjacent]);
        let with_ih = d.lam_fv(ih_fv, ih_ty, body);
        let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
        d.lam_fv(x_fv, nat, with_hx)
    };
    d.const_app(nat_p.le_rec, &[i, motive, minor_refl, minor_step, j, h])
}

/// `CReal.meshLevelCount_ge_of_size : ∀ (c outer j : Nat),
/// Nat.le (Nat.add (Nat.size c) (Nat.size outer)) j →
/// Nat.le (Nat.add (Nat.mul (Nat.succ c) outer) c) (CReal.meshLevelCount j)`
/// — the `Nat` half of rung 6c, and the reason the accuracy schedule can stay
/// additive.
///
/// The right-hand side is exactly [`CRealPrelude::mesh_le_of_ge`]'s threshold
/// at `c := CReal.bound (b − a)`; the left is a bit-count sum. Every step is
/// forced:
///
/// - `Nat.lt_pow_size` twice: `succ c ≤ 2^(size c)` and `succ outer ≤
///   2^(size outer)`.
/// - `mul_le_mul_left` twice (with `mul_comm` for the side this kernel does
///   not state): `(c+1)·(outer+1) ≤ 2^(size c)·2^(size outer)`.
/// - `pow_add` read RIGHT to LEFT: that product is `2^(size c + size outer)`.
/// - [`pow_two_mono`] carries it up to `2^j`.
/// - `mesh_level_count_pow` read RIGHT to LEFT: `2^j = succ (meshLevelCount j)`.
/// - `le_of_succ_le_succ` strips the successor, and the two rewrites it needs
///   on the left are both `Eq.refl` — `mul n (succ m)` and `add x (succ c)`
///   each reduce, because `Nat.mul` and `Nat.add` both recurse on their RIGHT
///   argument. Had the schedule been written multiplicatively those would have
///   been theorems instead.
fn declare_mesh_level_count_ge_of_size_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_p = p.rat.int.nat;
    let two = d.num(2);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let outer_fv = d.fresh_fvar();
    let outer = d.kernel().fvar(outer_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let sc = d.const_app(nat_p.size, &[c]);
    let so = d.const_app(nat_p.size, &[outer]);
    let sum_exp = NatOps::add(d, sc, so);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.le(sum_exp, j);

    let succ_c = d.succ(c);
    let succ_outer = d.succ(outer);
    let prod = NatOps::mul(d, succ_c, succ_outer);
    let pow_sc = d.const_app(nat_p.pow, &[two, sc]);
    let pow_so = d.const_app(nat_p.pow, &[two, so]);

    // step1 : (c+1)·(outer+1) ≤ (c+1)·2^(size outer).
    let h2 = d.lemma(nat_p.lt_pow_size, &[outer]);
    let mid = NatOps::mul(d, succ_c, pow_so);
    let step1 = d.lemma(nat_p.mul_le_mul_left, &[succ_c, succ_outer, pow_so, h2]);

    // step2 : (c+1)·2^(size outer) ≤ 2^(size c)·2^(size outer), via the
    // commuted form (this kernel states `mul_le_mul_left` only).
    let h1 = d.lemma(nat_p.lt_pow_size, &[c]);
    let step2 = {
        let raw = d.lemma(nat_p.mul_le_mul_left, &[pow_so, succ_c, pow_sc, h1]);
        let lhs_raw = NatOps::mul(d, pow_so, succ_c);
        let rhs_raw = NatOps::mul(d, pow_so, pow_sc);
        let rhs = NatOps::mul(d, pow_sc, pow_so);
        let comm_l = d.lemma(nat_p.mul_comm, &[pow_so, succ_c]);
        let comm_r = d.lemma(nat_p.mul_comm, &[pow_so, pow_sc]);
        let after_l = nat_rewrite_prop(d, lhs_raw, mid, comm_l, raw, &|d, z| d.le(z, rhs_raw));
        nat_rewrite_prop(d, rhs_raw, rhs, comm_r, after_l, &|d, z| d.le(mid, z))
    };

    let prod_pow = NatOps::mul(d, pow_sc, pow_so);
    let step3 = d.lemma(nat_p.le_trans, &[prod, mid, prod_pow, step1, step2]);

    // step4 : rewrite `2^(size c)·2^(size outer)` back to `2^(size c + size
    // outer)` — `pow_add` runs the other way, so it is used symmetrically.
    let pow_sum = d.const_app(nat_p.pow, &[two, sum_exp]);
    let step4 = {
        let fwd = d.lemma(nat_p.pow_add, &[two, sc, so]);
        let back = d.symm(pow_sum, prod_pow, fwd);
        nat_rewrite_prop(d, prod_pow, pow_sum, back, step3, &|d, z| d.le(prod, z))
    };

    let pow_j = d.const_app(nat_p.pow, &[two, j]);
    let climb = pow_two_mono(d, p, sum_exp, j, h);
    let step5 = d.lemma(nat_p.le_trans, &[prod, pow_sum, pow_j, step4, climb]);

    // step6 : `2^j = succ (meshLevelCount j)`, again read right to left.
    let mlc = d.const_app(p.mesh_level_count, &[j]);
    let succ_mlc = d.succ(mlc);
    let step6 = {
        let fwd = d.lemma(p.mesh_level_count_pow, &[j]);
        let back = d.symm(succ_mlc, pow_j, fwd);
        nat_rewrite_prop(d, pow_j, succ_mlc, back, step5, &|d, z| d.le(prod, z))
    };

    // `prod ≡ succ (mul (succ c) outer + c)` by `Nat.mul`/`Nat.add` both
    // recursing on the right, so `le_of_succ_le_succ` applies directly.
    let me = NatOps::mul(d, succ_c, outer);
    let threshold = NatOps::add(d, me, c);
    let proof = d.lemma(nat_p.le_of_succ_le_succ, &[threshold, mlc, step6]);

    let concl = d.le(threshold, mlc);
    let ty = {
        let out = d.arrow(h_ty, concl);
        let out = d.pi_fv(j_fv, nat, out);
        let out = d.pi_fv(outer_fv, nat, out);
        d.pi_fv(c_fv, nat, out)
    };
    let value = {
        let out = d.lam_fv(h_fv, h_ty, proof);
        let out = d.lam_fv(j_fv, nat, out);
        let out = d.lam_fv(outer_fv, nat, out);
        d.lam_fv(c_fv, nat, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_level_count_ge_of_size,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.meshLevelCount_ge_of_size` alone (a one-declaration
/// `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_level_count_ge_of_size(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_level_count_ge_of_size_thm(d, p)
}

/// `CReal.meshMax_le_add_of_modulus : ∀ F a b (u : UniformlyContinuousOn F a
/// b) (n j d : Nat), le a b → Nat.le (Nat.add (Nat.size (CReal.bound (add b
/// (neg a)))) (Nat.size (UniformlyContinuousOn.modulus F a b u n))) j → le
/// (meshMax F a b (Nat.add j d)) (add (meshMax F a b j) (ofRat (natDivSucc 1
/// n)))` — **rung 6's remaining owe, discharged.**
///
/// [`CRealPrelude::mesh_max_le_add_of_step_close`] left exactly one
/// obligation behind, and its own field documentation names it: "what a
/// `supOn` assembly still owes is only the instantiation of `hclose` from
/// `uc_spec` at the accuracy `expOfModulus` selects". This is that
/// instantiation. No mesh geometry survives into the hypothesis — the only
/// condition is a `Nat` bit-count inequality on the level `j`.
///
/// The chain, all of it existing machinery:
///
/// - `hstep : le y (add x Δⱼ)` plus [`CRealPrelude::mesh_le_of_ge`] (through
///   [`CRealPrelude::mesh_level_count_ge_of_size`], which converts the level
///   `j` into that lemma's Archimedean threshold) gives `le y (add x (ofRat
///   (1/(modulus n + 1))))`.
/// - `hxy : le x y` plus [`CRealPrelude::le_add_of_nonneg`] gives the other
///   side, and [`CRealPrelude::abs_le_of_two_sided`] folds the pair into the
///   `close_within` shape [`CRealPrelude::uc_spec`] consumes.
/// - `uc_spec` is applied at `(x := y, y := x)` — its conclusion bounds
///   `|F x − F y|` with the FIRST argument on the left, and `hclose` wants
///   `F y` on the left — and [`CRealPrelude::le_add_of_abs_sub_le`] turns that
///   back into the one-sided form.
///
/// **`eps` is `ofRat (natDivSucc 1 n)`, i.e. `1/(n+1)`, at a FREELY CHOSEN
/// `n`.** That is what makes this summable later: a caller takes `n :=
/// meshLevelCount k`, so `eps = 1/2^k` (the doubling schedule reused as the
/// requested ACCURACY index, rung 5's whole point), and the harmonic trap the
/// module documentation warns about never arises. Nothing here forces that
/// choice, so the lemma stays usable at any accuracy.
fn declare_mesh_max_le_add_of_modulus_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;
    let rat = p.rat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let dd_fv = d.fresh_fvar();
    let dd = d.kernel().fvar(dd_fv);

    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);

    // `outer := UniformlyContinuousOn.modulus F a b u n`, the accuracy the
    // witness itself demands; `c := CReal.bound (b − a)`, read straight off
    // the total projection rather than out of `CReal.archimedean`'s `Exists`.
    let outer = d.const_app(p.uc_modulus, &[f, a, b, u, n]);
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let c = d.const_app(p.bound, &[width]);

    let size_c = d.const_app(nat_p.size, &[c]);
    let size_outer = d.const_app(nat_p.size, &[outer]);
    let size_sum = NatOps::add(d, size_c, size_outer);
    let hsize_fv = d.fresh_fvar();
    let hsize = d.kernel().fvar(hsize_fv);
    let hsize_ty = d.le(size_sum, j);

    let one_nat = d.num(1);
    let q_rat = d.const_app(rat.nat_div_succ, &[one_nat, outer]);
    let q_real = embed(d, p, q_rat);
    let eps_rat = d.const_app(rat.nat_div_succ, &[one_nat, n]);
    let eps = embed(d, p, eps_rat);

    let mlc_j = d.const_app(p.mesh_level_count, &[j]);
    let delta_j = mesh_delta(d, p, a, b, mlc_j);

    // `Δⱼ ≤ 1/(outer + 1)`: the level clears `mesh_le_of_ge`'s threshold.
    let threshold_ok = d.lemma(p.mesh_level_count_ge_of_size, &[c, outer, j, hsize]);
    let delta_le_q = d.lemma(p.mesh_le_of_ge, &[a, b, outer, mlc_j, hab, threshold_ok]);

    let hclose_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax = cle(d, p, a, x);
        let hxb = cle(d, p, x, b);
        let hay = cle(d, p, a, y);
        let hyb = cle(d, p, y, b);
        let hxy = cle(d, p, x, y);
        let shifted = cadd(d, p, x, delta_j);
        let hstep = cle(d, p, y, shifted);
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let padded = cadd(d, p, fx, eps);
        let concl = cle(d, p, fy, padded);
        let out = d.arrow(hstep, concl);
        let out = d.arrow(hxy, out);
        let out = d.arrow(hyb, out);
        let out = d.arrow(hay, out);
        let out = d.arrow(hxb, out);
        let out = d.arrow(hax, out);
        let over_y = d.pi_fv(y_fv, carrier, out);
        d.pi_fv(x_fv, carrier, over_y)
    };

    let hclose = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hax_ty = cle(d, p, a, x);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);
        let hxb_ty = cle(d, p, x, b);
        let hay_fv = d.fresh_fvar();
        let hay = d.kernel().fvar(hay_fv);
        let hay_ty = cle(d, p, a, y);
        let hyb_fv = d.fresh_fvar();
        let hyb = d.kernel().fvar(hyb_fv);
        let hyb_ty = cle(d, p, y, b);
        let hxy_fv = d.fresh_fvar();
        let hxy = d.kernel().fvar(hxy_fv);
        let hxy_ty = cle(d, p, x, y);
        let hstep_fv = d.fresh_fvar();
        let hstep = d.kernel().fvar(hstep_fv);
        let shifted_delta = cadd(d, p, x, delta_j);
        let hstep_ty = cle(d, p, y, shifted_delta);

        // `y ≤ x + Δⱼ ≤ x + 1/(outer+1)`.
        let shifted_q = cadd(d, p, x, q_real);
        let refl_x = d.lemma(p.le_refl, &[x]);
        let widen = d.lemma(p.add_le_add, &[x, x, delta_j, q_real, refl_x, delta_le_q]);
        let y_le = d.lemma(p.le_trans, &[y, shifted_delta, shifted_q, hstep, widen]);

        // `x ≤ y ≤ y + 1/(outer+1)`.
        let q_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, outer]);
        let y_grow = d.lemma(p.le_add_of_nonneg, &[y, q_rat, q_nonneg]);
        let shifted_y = cadd(d, p, y, q_real);
        let x_le = d.lemma(p.le_trans, &[x, y, shifted_y, hxy, y_grow]);

        // Fold the pair into `close_within y x (1/(outer+1))`, which is the
        // shape `uc_spec` consumes, at `(x := y, y := x)`.
        let closeness = d.lemma(p.abs_le_of_two_sided, &[y, x, q_rat, y_le, x_le]);
        let spec = d.const_app(
            p.uc_spec,
            &[f, a, b, u, n, y, x, hay, hyb, hax, hxb, closeness],
        );
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let body = d.lemma(p.le_add_of_abs_sub_le, &[fy, fx, eps_rat, spec]);

        let out = d.lam_fv(hstep_fv, hstep_ty, body);
        let out = d.lam_fv(hxy_fv, hxy_ty, out);
        let out = d.lam_fv(hyb_fv, hyb_ty, out);
        let out = d.lam_fv(hay_fv, hay_ty, out);
        let out = d.lam_fv(hxb_fv, hxb_ty, out);
        let out = d.lam_fv(hax_fv, hax_ty, out);
        let over_y = d.lam_fv(y_fv, carrier, out);
        d.lam_fv(x_fv, carrier, over_y)
    };
    let _ = hclose_ty;

    let proof = d.lemma(
        p.mesh_max_le_add_of_step_close,
        &[f, a, b, j, dd, eps, hab, hclose],
    );

    let level = NatOps::add(d, j, dd);
    let mesh_l = d.const_app(p.mesh_max, &[f, a, b, level]);
    let mesh_j = d.const_app(p.mesh_max, &[f, a, b, j]);
    let rhs = cadd(d, p, mesh_j, eps);
    let conclusion = cle(d, p, mesh_l, rhs);

    let ty = {
        let out = d.arrow(hsize_ty, conclusion);
        let out = d.arrow(hab_ty, out);
        let out = d.pi_fv(dd_fv, nat, out);
        let out = d.pi_fv(j_fv, nat, out);
        let out = d.pi_fv(n_fv, nat, out);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(hsize_fv, hsize_ty, proof);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(dd_fv, nat, out);
        let out = d.lam_fv(j_fv, nat, out);
        let out = d.lam_fv(n_fv, nat, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_max_le_add_of_modulus,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.meshMax_le_add_of_modulus` alone (a one-declaration
/// `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_max_le_add_of_modulus(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_max_le_add_of_modulus_thm(d, p)
}

// ---------------------------------------------------------------------------
// Rung 6e: the SUP SEQUENCE, and the estimate `supOn`'s `CReal.mk` consumes.
//
// A CORRECTION to this module's "Rung 6 re-verified" section, which sizes what
// follows the gap bound as a telescope -- "sum the per-level gaps", and, in the
// worst case, a DOUBLE telescope across the unboundedly many mesh levels one
// `k`-to-`k+1` block can span.
//
// No telescope is needed, and none is built here. The reason is that rung 6's
// gap bound is already DEPTH-UNIFORM: `meshMax_le_add_of_step_close` takes an
// arbitrary refinement depth `d` and bounds `meshMax (j + d)` against
// `meshMax j`, with the SAME epsilon at every depth. That is exactly what
// `meshPoint_near_coarse`'s arbitrary-depth statement bought. So the estimate
// at `k' >= k` is one application of `meshMax_le_add_of_modulus`, not a sum of
// applications, and how many doublings `trueExpOfModulus` jumps between `k` and
// `k'` never enters. The double telescope the module doc contemplates would
// have been machinery for a difficulty that the previous rung had already
// removed.
//
// What is left is genuinely small:
//
//   supSeq k' - supSeq k <= 1/2^k     (rung 6, depth-uniform, one application)
//   supSeq k  - supSeq k' <= 0        (`meshMax_mono`)
//
// for every `k <= k'` -- a two-sided bound with a geometric modulus, which is
// `cauchy_of_abs_diff_le`'s hypothesis after one antitonicity step turning
// `1/2^k` into `1/(k+1)`.
// ---------------------------------------------------------------------------

/// `CReal.supLevel : ∀ F a b, UniformlyContinuousOn F a b → Nat → Nat :=
/// fun F a b u k => Nat.add (Nat.size (CReal.bound (add b (neg a))))
/// (CReal.trueExpOfModulus (UniformlyContinuousOn.modulus F a b u) k)` — the
/// mesh level the sup sequence samples at accuracy index `k`.
///
/// Two summands, one per factor of
/// [`CRealPrelude::mesh_level_count_ge_of_size`]'s threshold:
/// `Nat.size (CReal.bound (b − a))` covers the INTERVAL WIDTH (constant in
/// `k`, so it does not disturb monotonicity), and
/// [`CRealPrelude::true_exp_of_modulus`] covers the MODULUS at the requested
/// accuracy. Additive precisely so that
/// [`CRealPrelude::exp_of_modulus_le_true_exp_of_modulus`] composes with
/// `Nat.add_le_add_left` and nothing has to be recomputed.
///
/// The width term is what rung 5's `expOfModulus` schedule does NOT carry, and
/// omitting it would make the whole construction correct only on intervals of
/// width at most one — see this file's rung 6e commit message.
fn declare_sup_level_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let c = d.const_app(p.bound, &[width]);
    let size_c = d.const_app(nat_p.size, &[c]);
    let modulus = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let te = d.const_app(p.true_exp_of_modulus, &[modulus, k]);
    let body = NatOps::add(d, size_c, te);

    let ty = {
        let out = d.arrow(nat, nat);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(k_fv, nat, body);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sup_level,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// `CReal.supSeq : ∀ F a b, UniformlyContinuousOn F a b → Nat → CReal :=
/// fun F a b u k => CReal.meshMax F a b (CReal.supLevel F a b u k)` — the
/// sequence whose limit is the supremum of `F` on `[a, b]`.
///
/// **This is a VALUE, never an argmax.** Each term is a finite maximum over a
/// mesh, so it is a height; nothing here names or produces a point at which
/// that height is attained, and
/// [`ExtremeValueNames::evt_attained_max_decides_sign`] says no construction can
/// (`creal/extreme_value.rs`). See this module's own value/argmax section.
fn declare_sup_seq_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let level = d.const_app(p.sup_level, &[f, a, b, u, k]);
    let body = d.const_app(p.mesh_max, &[f, a, b, level]);

    let ty = {
        let out = d.arrow(nat, carrier);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(k_fv, nat, body);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sup_seq,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// `CReal.supLevel_mono : ∀ F a b u k k', Nat.le k k' →
/// Nat.le (supLevel F a b u k) (supLevel F a b u k')`.
///
/// [`CRealPrelude::true_exp_of_modulus_mono`] under a constant offset:
/// `Nat.add_le_add_left` moves the width term through untouched, which is the
/// whole reason [`declare_sup_level_def`] is additive rather than folding the
/// width into the modulus.
fn declare_sup_level_mono_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kp_fv = d.fresh_fvar();
    let kp = d.kernel().fvar(kp_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.le(k, kp);

    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let c = d.const_app(p.bound, &[width]);
    let size_c = d.const_app(nat_p.size, &[c]);
    let modulus = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let te_k = d.const_app(p.true_exp_of_modulus, &[modulus, k]);
    let te_kp = d.const_app(p.true_exp_of_modulus, &[modulus, kp]);

    let inner = d.lemma(p.true_exp_of_modulus_mono, &[modulus, k, kp, h]);
    let proof = d.lemma(nat_p.add_le_add_left, &[size_c, te_k, te_kp, inner]);

    let lvl_k = d.const_app(p.sup_level, &[f, a, b, u, k]);
    let lvl_kp = d.const_app(p.sup_level, &[f, a, b, u, kp]);
    let concl = d.le(lvl_k, lvl_kp);

    let ty = {
        let out = d.arrow(h_ty, concl);
        let out = d.pi_fv(kp_fv, nat, out);
        let out = d.pi_fv(k_fv, nat, out);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(h_fv, h_ty, proof);
        let out = d.lam_fv(kp_fv, nat, out);
        let out = d.lam_fv(k_fv, nat, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_level_mono,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.supSeq_mono : ∀ F a b u, le a b → ∀ k k', Nat.le k k' →
/// le (supSeq F a b u k) (supSeq F a b u k')` — the sup sequence increases.
///
/// [`CRealPrelude::mesh_max_mono`] at [`CRealPrelude::sup_level_mono`]'s two
/// levels. This is the LOWER half of the Cauchy estimate, and it is exact
/// (no epsilon): refining a mesh can only add sample points, never remove
/// them.
fn declare_sup_seq_mono_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kp_fv = d.fresh_fvar();
    let kp = d.kernel().fvar(kp_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.le(k, kp);

    let lvl_k = d.const_app(p.sup_level, &[f, a, b, u, k]);
    let lvl_kp = d.const_app(p.sup_level, &[f, a, b, u, kp]);
    let hlevel = d.lemma(p.sup_level_mono, &[f, a, b, u, k, kp, h]);
    let proof = d.lemma(p.mesh_max_mono, &[f, a, b, u, hab, lvl_k, lvl_kp, hlevel]);

    let seq_k = d.const_app(p.sup_seq, &[f, a, b, u, k]);
    let seq_kp = d.const_app(p.sup_seq, &[f, a, b, u, kp]);
    let concl = cle(d, p, seq_k, seq_kp);

    let ty = {
        let out = d.arrow(h_ty, concl);
        let out = d.pi_fv(kp_fv, nat, out);
        let out = d.pi_fv(k_fv, nat, out);
        let out = d.arrow(hab_ty, out);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(h_fv, h_ty, proof);
        let out = d.lam_fv(kp_fv, nat, out);
        let out = d.lam_fv(k_fv, nat, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_seq_mono,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.supSeq_le_add : ∀ F a b u, le a b → ∀ k k', Nat.le k k' →
/// le (supSeq F a b u k') (add (supSeq F a b u k) (ofRat (natDivSucc 1
/// (meshLevelCount k))))` — the UPPER half of the Cauchy estimate, at the
/// geometric rate `1/2^k`.
///
/// **One application of [`CRealPrelude::mesh_max_le_add_of_modulus`], not a
/// telescope.** The gap bound is uniform in refinement depth, so however many
/// doublings [`CRealPrelude::true_exp_of_modulus`] jumps between `k` and `k'`,
/// the same epsilon covers all of them at once. `Nat.le_dest` turns
/// `supLevel k ≤ supLevel k'` into the `add j d` shape the gap bound is stated
/// in; that elimination is `Exists.rec` into a `Prop`, which kernel fact 2
/// permits — the restriction bites only at `supOn`'s own `CReal.mk`, where
/// `K` and the sequence are DATA.
///
/// The accuracy is requested at `n := meshLevelCount k`, so the epsilon is
/// `1/(meshLevelCount k + 1) = 1/2^k`: rung 5's doubling schedule reused as
/// the ACCURACY index, which is the whole reason the harmonic-series trap
/// never appears. The hypothesis
/// `Nat.le (size (bound (b−a)) + size (modulus (meshLevelCount k)))
/// (supLevel k)` is discharged by definitional unfolding —
/// `expOfModulus m k` IS `Nat.size (m (meshLevelCount k))` — plus
/// [`CRealPrelude::exp_of_modulus_le_true_exp_of_modulus`] under
/// `Nat.add_le_add_left`.
fn declare_sup_seq_le_add_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;
    let rat = p.rat;
    let logic = p.rat.int.logic;
    let one_level = d.level_one();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kp_fv = d.fresh_fvar();
    let kp = d.kernel().fvar(kp_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.le(k, kp);

    let lvl_k = d.const_app(p.sup_level, &[f, a, b, u, k]);
    let lvl_kp = d.const_app(p.sup_level, &[f, a, b, u, kp]);
    let hlevel = d.lemma(p.sup_level_mono, &[f, a, b, u, k, kp, h]);

    let one_nat = d.num(1);
    let mlc_k = d.const_app(p.mesh_level_count, &[k]);
    let eps_rat = d.const_app(rat.nat_div_succ, &[one_nat, mlc_k]);
    let eps = embed(d, p, eps_rat);

    let seq_k = d.const_app(p.sup_seq, &[f, a, b, u, k]);
    let seq_kp = d.const_app(p.sup_seq, &[f, a, b, u, kp]);
    let rhs = cadd(d, p, seq_k, eps);
    let concl = cle(d, p, seq_kp, rhs);

    // `hsize` at the requested accuracy `meshLevelCount k`. Stated in
    // `expOfModulus` form; the kernel's own delta unfolding matches it against
    // `mesh_max_le_add_of_modulus`'s `Nat.size (modulus (meshLevelCount k))`.
    let modulus = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let c = d.const_app(p.bound, &[width]);
    let size_c = d.const_app(nat_p.size, &[c]);
    let exp_k = d.const_app(p.exp_of_modulus, &[modulus, k]);
    let te_k = d.const_app(p.true_exp_of_modulus, &[modulus, k]);
    let exp_le = d.lemma(p.exp_of_modulus_le_true_exp_of_modulus, &[modulus, k]);
    let hsize = d.lemma(nat_p.add_le_add_left, &[size_c, exp_k, te_k, exp_le]);

    // `∃ dd, supLevel k + dd = supLevel k'`.
    let predicate = {
        let dd_fv = d.fresh_fvar();
        let dd = d.kernel().fvar(dd_fv);
        let sum = NatOps::add(d, lvl_k, dd);
        let eq = d.kernel().const_(logic.eq, vec![one_level]);
        let body = d.apply(eq, &[nat, sum, lvl_kp]);
        d.lam_fv(dd_fv, nat, body)
    };
    let hdest = d.lemma(nat_p.le_dest, &[lvl_k, lvl_kp, hlevel]);

    let minor = {
        let dd_fv = d.fresh_fvar();
        let dd = d.kernel().fvar(dd_fv);
        let hdd_fv = d.fresh_fvar();
        let hdd = d.kernel().fvar(hdd_fv);
        let sum = NatOps::add(d, lvl_k, dd);
        let eq = d.kernel().const_(logic.eq, vec![one_level]);
        let hdd_ty = d.apply(eq, &[nat, sum, lvl_kp]);

        let gap = d.lemma(
            p.mesh_max_le_add_of_modulus,
            &[f, a, b, u, mlc_k, lvl_k, dd, hab, hsize],
        );
        let moved = nat_rewrite_prop(d, sum, lvl_kp, hdd, gap, &|d, z| {
            let mesh_z = d.const_app(p.mesh_max, &[f, a, b, z]);
            cle(d, p, mesh_z, rhs)
        });
        let with_hdd = d.lam_fv(hdd_fv, hdd_ty, moved);
        d.lam_fv(dd_fv, nat, with_hdd)
    };
    let proof = exists_elim(d, predicate, concl, hdest, minor);

    let ty = {
        let out = d.arrow(h_ty, concl);
        let out = d.pi_fv(kp_fv, nat, out);
        let out = d.pi_fv(k_fv, nat, out);
        let out = d.arrow(hab_ty, out);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(h_fv, h_ty, proof);
        let out = d.lam_fv(kp_fv, nat, out);
        let out = d.lam_fv(k_fv, nat, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_seq_le_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.supLevel`, `CReal.supSeq` and their three order facts.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sup_seq(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_sup_level_def(d, p)?;
    declare_sup_seq_def(d, p)?;
    declare_sup_level_mono_thm(d, p)?;
    declare_sup_seq_mono_thm(d, p)?;
    declare_sup_seq_le_add_thm(d, p)
}

// ---------------------------------------------------------------------------
// Rung 6f: `Cauchy (supSeq F a b u)`.
//
// The two halves of rung 6e are already a two-sided estimate; all that stands
// between them and `cauchy_of_abs_diff_le`'s hypothesis is turning the
// geometric rate `1/2^k` into the harmonic `1/(k+1)` the criterion is stated
// in. That is `Rat.natDivSucc_antitone` applied to `k <= meshLevelCount k`,
// which is `Nat.self_lt_two_pow` read through `meshLevelCount_pow`.
//
// Note the direction: the schedule REQUESTS the summable `1/2^k` and then
// WEAKENS it to `1/(k+1)` for the criterion. Requesting `1/(k+1)` directly is
// the harmonic trap rung 5 exists to avoid -- it is fine as a Cauchy MODULUS
// and fatal as a per-level GAP, because the gaps would have had to be summed.
// Rung 6e's depth-uniformity is what lets both readings coexist.
// ---------------------------------------------------------------------------

/// `CReal.le_meshLevelCount : ∀ (m : Nat), Nat.le m (CReal.meshLevelCount m)`
/// — `m ≤ 2^m − 1`, i.e. the doubling schedule outruns its own index.
///
/// [`NatPrelude::self_lt_two_pow`](crate::NatPrelude::self_lt_two_pow) states
/// `Lt m (pow 2 m)`, which is `Nat.le (succ m) (pow 2 m)` after `Nat.lt`'s
/// unfold; [`CRealPrelude::mesh_level_count_pow`] rewrites `pow 2 m` to
/// `succ (meshLevelCount m)` and `le_of_succ_le_succ` strips the successor.
fn declare_le_mesh_level_count_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_p = p.rat.int.nat;
    let two = d.num(2);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let pow_m = d.const_app(nat_p.pow, &[two, m]);
    let mlc = d.const_app(p.mesh_level_count, &[m]);
    let succ_mlc = d.succ(mlc);
    let succ_m = d.succ(m);

    let strict = d.lemma(nat_p.self_lt_two_pow, &[m]);
    let fwd = d.lemma(p.mesh_level_count_pow, &[m]);
    let back = d.symm(succ_mlc, pow_m, fwd);
    let moved = nat_rewrite_prop(d, pow_m, succ_mlc, back, strict, &|d, z| d.le(succ_m, z));
    let proof = d.lemma(nat_p.le_of_succ_le_succ, &[m, mlc, moved]);

    let concl = d.le(m, mlc);
    let ty = d.pi_fv(m_fv, nat, concl);
    let value = d.lam_fv(m_fv, nat, proof);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.le_mesh_level_count,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.le x (Rat.add x y)` from `hy : Rat.le Rat.zero y`.
///
/// ADR-1592 retirement: was a hand `le_refl`+`add_le_add`+`add_zero`
/// rewrite chain; now routed through `linarith::generic::prove_s` over
/// `AlgS.Rat.orderedRingS` (`super::linarith_bridge::rat_le_add_right`) —
/// the SAME fact, the SAME type, reached generically.
fn rat_le_add_right(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    hy: ExprId,
) -> ExprId {
    super::linarith_bridge::rat_le_add_right(d, p, x, y, hy)
}

/// `Rat.le y (Rat.add x y)` from `hx : Rat.le Rat.zero x`.
fn rat_le_add_left(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    hx: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero = rzero(d, rat);
    let refl_y = d.lemma(rat.le_refl, &[y]);
    let widened = d.lemma(rat.add_le_add, &[zero, x, y, y, hx, refl_y]);
    let padded = radd(d, zero, y);
    let sum = radd(d, x, y);
    let trim = d.lemma(rat.zero_add, &[y]);
    rat_eq_rewrite(d, padded, y, trim, widened, &|d, t| rle(d, rat, t, sum))
}

/// `CReal.supSeq_abs_diff_le : ∀ F a b u, le a b → ∀ m n,
/// le (abs (add (supSeq F a b u m) (neg (supSeq F a b u n))))
/// (ofRat (Rat.add (natDivSucc 1 m) (natDivSucc 1 n)))` — the two-sided
/// estimate in exactly [`CRealPrelude::cauchy_of_abs_diff_le`]'s shape, at
/// `K := 1`.
///
/// `Nat.le_total` splits on which index is coarser; the two branches are
/// mirror images, and in each the EASY side is
/// [`CRealPrelude::sup_seq_mono`] (the sequence increases, so one difference
/// is already `≤ 0`) while the WORKING side is
/// [`CRealPrelude::sup_seq_le_add`] weakened from `1/2^k` to `1/(k+1)` by
/// [`CRealPrelude::le_mesh_level_count`] under `Rat.natDivSucc_antitone`, then
/// padded to the full two-term bound.
///
/// `K = 1` is not a tuning choice — it is what the geometric schedule buys.
/// A per-level rate that only summed to `O(1/k)` would need `K` to grow.
fn declare_sup_seq_abs_diff_le_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;
    let rat = p.rat;
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one_nat = d.num(1);
    let frac_m = d.const_app(rat.nat_div_succ, &[one_nat, m]);
    let frac_n = d.const_app(rat.nat_div_succ, &[one_nat, n]);
    let q_rat = radd(d, frac_m, frac_n);
    let q_real = embed(d, p, q_rat);

    let seq_m = d.const_app(p.sup_seq, &[f, a, b, u, m]);
    let seq_n = d.const_app(p.sup_seq, &[f, a, b, u, n]);

    let nonneg_m = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, m]);
    let nonneg_n = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, n]);

    // `1/2^k ≤ 1/(k+1)` for `k ∈ {m, n}` — the geometric-to-harmonic step.
    let geom_le = |d: &mut IntDev<'_>, k: ExprId| -> (ExprId, ExprId) {
        let mlc_k = d.const_app(p.mesh_level_count, &[k]);
        let geom = d.const_app(rat.nat_div_succ, &[one_nat, mlc_k]);
        let hk = d.lemma(p.le_mesh_level_count, &[k]);
        let anti = d.lemma(rat.nat_div_succ_antitone, &[k, mlc_k, hk]);
        (geom, anti)
    };

    // The "easy" direction at `(coarse, fine)`: `supSeq coarse ≤ supSeq fine
    // ≤ supSeq fine + q`.
    let easy = |d: &mut IntDev<'_>, coarse: ExprId, fine: ExprId, hle: ExprId| -> ExprId {
        let sc = d.const_app(p.sup_seq, &[f, a, b, u, coarse]);
        let sf = d.const_app(p.sup_seq, &[f, a, b, u, fine]);
        let mono = d.lemma(p.sup_seq_mono, &[f, a, b, u, hab, coarse, fine, hle]);
        // `0 ≤ 1/(m+1) ≤ 1/(m+1) + 1/(n+1)`.
        let zero_le_q = {
            let step = rat_le_add_right(d, p, frac_m, frac_n, nonneg_n);
            let zero = rzero(d, rat);
            d.lemma(rat.le_trans, &[zero, frac_m, q_rat, nonneg_m, step])
        };
        let grow = d.lemma(p.le_add_of_nonneg, &[sf, q_rat, zero_le_q]);
        let padded = cadd(d, p, sf, q_real);
        d.lemma(p.le_trans, &[sc, sf, padded, mono, grow])
    };

    // The "working" direction at `(coarse, fine)`: `supSeq fine ≤ supSeq
    // coarse + 1/2^coarse ≤ supSeq coarse + q`, where `q` must dominate
    // `1/(coarse+1)`; `pick` says which summand of `q` that is.
    let working = |d: &mut IntDev<'_>,
                   coarse: ExprId,
                   fine: ExprId,
                   hle: ExprId,
                   frac_coarse: ExprId,
                   pick: ExprId|
     -> ExprId {
        let sc = d.const_app(p.sup_seq, &[f, a, b, u, coarse]);
        let sf = d.const_app(p.sup_seq, &[f, a, b, u, fine]);
        let (geom, anti) = geom_le(d, coarse);
        let geom_le_q = d.lemma(rat.le_trans, &[geom, frac_coarse, q_rat, anti, pick]);
        let geom_real = embed(d, p, geom);
        let lift = d.lemma(p.of_rat_le, &[geom, q_rat, geom_le_q]);
        let step = d.lemma(p.sup_seq_le_add, &[f, a, b, u, hab, coarse, fine, hle]);
        let refl_sc = d.lemma(p.le_refl, &[sc]);
        let widen = d.lemma(p.add_le_add, &[sc, sc, geom_real, q_real, refl_sc, lift]);
        let mid = cadd(d, p, sc, geom_real);
        let padded = cadd(d, p, sc, q_real);
        d.lemma(p.le_trans, &[sf, mid, padded, step, widen])
    };

    let diff = {
        let neg_n = cneg(d, p, seq_n);
        cadd(d, p, seq_m, neg_n)
    };
    let abs_diff = d.const_app(p.abs, &[diff]);
    let concl = cle(d, p, abs_diff, q_real);

    // `1/(m+1) ≤ q` and `1/(n+1) ≤ q`.
    let pick_m = rat_le_add_right(d, p, frac_m, frac_n, nonneg_n);
    let pick_n = rat_le_add_left(d, p, frac_m, frac_n, nonneg_m);

    let le_mn_ty = d.le(m, n);
    let le_nm_ty = d.le(n, m);
    let split = d.lemma(nat_p.le_total, &[m, n]);

    let minor_mn = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        // `m ≤ n`: `supSeq m` is the coarse one.
        let side_m = easy(d, m, n, h);
        let side_n = working(d, m, n, h, frac_m, pick_m);
        let body = d.lemma(
            p.abs_le_of_two_sided,
            &[seq_m, seq_n, q_rat, side_m, side_n],
        );
        d.lam_fv(h_fv, le_mn_ty, body)
    };
    let minor_nm = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        // `n ≤ m`: `supSeq n` is the coarse one, so the roles flip.
        let side_m = working(d, n, m, h, frac_n, pick_n);
        let side_n = easy(d, n, m, h);
        let body = d.lemma(
            p.abs_le_of_two_sided,
            &[seq_m, seq_n, q_rat, side_m, side_n],
        );
        d.lam_fv(h_fv, le_nm_ty, body)
    };
    let proof = d.lemma(
        logic.or_elim,
        &[le_mn_ty, le_nm_ty, concl, split, minor_mn, minor_nm],
    );

    let ty = {
        let out = d.pi_fv(n_fv, nat, concl);
        let out = d.pi_fv(m_fv, nat, out);
        let out = d.arrow(hab_ty, out);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(n_fv, nat, proof);
        let out = d.lam_fv(m_fv, nat, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_seq_abs_diff_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.supSeq_cauchy : ∀ F a b u, le a b → Cauchy (supSeq F a b u)` — **the
/// mesh maxima of a uniformly continuous function on a compact interval
/// converge.**
///
/// One application of [`CRealPrelude::cauchy_of_abs_diff_le`] at `K := 1`.
/// This is EVT's constructive content as a `Prop`; turning it into the real
/// itself is the separate, purely mechanical `CReal.mk`/`speedup` step, which
/// needs the same estimate restated on canonical SAMPLES rather than as a
/// real-valued bound.
fn declare_sup_seq_cauchy_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);

    let seq = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.sup_seq, &[f, a, b, u, k]);
        d.lam_fv(k_fv, nat, body)
    };
    let one_nat = d.num(1);
    let estimate = d.lemma(p.sup_seq_abs_diff_le, &[f, a, b, u, hab]);
    let proof = d.lemma(p.cauchy_of_abs_diff_le, &[seq, one_nat, estimate]);
    let concl = d.const_app(p.cauchy, &[seq]);

    let ty = {
        let out = d.arrow(hab_ty, concl);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(hab_fv, hab_ty, proof);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_seq_cauchy,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.le_meshLevelCount`, `CReal.supSeq_abs_diff_le` and
/// `CReal.supSeq_cauchy`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sup_seq_cauchy(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_le_mesh_level_count_thm(d, p)?;
    declare_sup_seq_abs_diff_le_thm(d, p)?;
    declare_sup_seq_cauchy_thm(d, p)
}

// ---------------------------------------------------------------------------
// Rung 7: `CReal.supOn`.
//
// Everything above is `Prop`. This is the step where the estimate becomes a
// REAL, and it is the one place kernel fact 1 bites: `K` and the sequence feed
// `CReal.speedup`, a `Type`-level construction, so neither may be pulled out of
// an existential. Both are concrete here -- `K` is the literal `3` and the
// sequence is `CReal.supSeq` applied to the given arguments -- so nothing is
// eliminated and `Exists.rec` never appears on the data path.
//
// The shape is `integral.rs`'s `declare_creal_integral` verbatim, one
// construction over: `CReal.mk (speedup (diagonal f) K) (regular_of_scaled_
// cauchy f K raw)`.
// ---------------------------------------------------------------------------

/// `CReal.supOn : ∀ F a b, le a b → UniformlyContinuousOn F a b → CReal` —
/// **the supremum of a uniformly continuous function on a compact interval,
/// produced rather than asserted to exist.**
///
/// EVT's row 1 under ADR-0603's grading. Its row 2,
/// [`ExtremeValueNames::evt_attained_max_decides_sign`], proves that a MAXIMISER
/// cannot be constructed; this is the maximum's VALUE, which can. Nothing in
/// this file names or produces a point at which the value is attained, and
/// nothing should — see the module documentation's value/argmax section.
///
/// `K := 3`, not a tuning constant: [`CRealPrelude::sup_seq_abs_diff_le`]
/// gives the real-valued estimate at `K = 1` (the geometric schedule's doing),
/// and [`CRealPrelude::scaled_cauchy_of_abs_diff_le`]'s canonical-sample index
/// shift costs exactly `+2`.
///
/// **The hypotheses, stated honestly.** `le a b` and a
/// `UniformlyContinuousOn` witness. The second is the constructive substitute
/// for "continuous on a compact set" and carries a MODULUS as data — this
/// kernel cannot derive one from pointwise continuity, and no constructive
/// development can. The first is ordinary. There is no Archimedean hypothesis
/// and no positivity side condition: the interval width is handled by
/// [`CRealPrelude::bound`], a total computable projection, inside
/// [`CRealPrelude::mesh_le_of_ge`].
fn declare_sup_on_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);

    let value_body = sup_on_body(d, p, f, a, b, hab, u);

    let ty = {
        let after_u = d.arrow(u_ty, carrier);
        let after_hab = d.arrow(hab_ty, after_u);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, func_ty, over_a)
    };
    let value = {
        let with_u = d.lam_fv(u_fv, u_ty, value_body);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, func_ty, over_a)
    };
    let _ = nat;
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sup_on,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// `CReal.mk (speedup (fun n => seq (supSeq F a b u n) n) 3)
/// (regular_of_scaled_cauchy (supSeq F a b u) 3 raw)` — `supOn`'s body, shared
/// with [`declare_sup_seq_converges_thm`] so that theorem's conclusion is the
/// SAME `ExprId` rather than merely defeq to it.
///
/// That sharing is deliberate. Rebuilding the `CReal.mk` term by hand on the
/// other side of the equation is what forces the kernel to delta-unfold the
/// whole `Definition` — the 18.7 s → 92.6 s regression this module's
/// neighbourhood already paid for once (`creal/integral.rs`'s
/// `riemannSum_integral_close`).
fn sup_on_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    hab: ExprId,
    u: ExprId,
) -> ExprId {
    let nat = d.nat_ty();

    let f_lambda = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.const_app(p.sup_seq, &[f, a, b, u, n]);
        d.lam_fv(n_fv, nat, body)
    };
    let one_nat = d.num(1);
    let k = d.num(3);

    let estimate = d.lemma(p.sup_seq_abs_diff_le, &[f, a, b, u, hab]);
    let raw = d.lemma(
        p.scaled_cauchy_of_abs_diff_le,
        &[f_lambda, one_nat, estimate],
    );
    let regularity = d.lemma(p.regular_of_scaled_cauchy, &[f_lambda, k, raw]);

    let diag = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f_lambda, &[n]);
        let body = d.const_app(p.seq, &[fn_term, n]);
        d.lam_fv(n_fv, nat, body)
    };
    let speedup_term = d.const_app(p.speedup, &[diag, k]);
    d.const_app(p.mk, &[speedup_term, regularity])
}

/// `CReal.supSeq_converges_supOn : ∀ F a b (hab : le a b) u,
/// Converges (supSeq F a b u) (supOn F a b hab u)` — **`supOn` is the limit of
/// the mesh maxima, not merely a well-typed `CReal.mk`.**
///
/// Without this, `supOn` would be an opaque construction whose only guarantee
/// is that the kernel accepted its regularity proof — and this file's own
/// documentation is emphatic that a `Definition` type-checking says nothing
/// about what it computes. This is the theorem that pins it.
///
/// One application of [`CRealPrelude::converges_of_scaled_cauchy`], whose
/// conclusion NAMES `CReal.mk (speedup (diagonal f) K) (regular_of_scaled_
/// cauchy f K h)` — the same term [`sup_on_body`] builds, from the same
/// arguments, so the two are the identical `ExprId` and the kernel never
/// unfolds `supOn`'s `Definition` to compare them.
fn declare_sup_seq_converges_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);

    let f_lambda = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.const_app(p.sup_seq, &[f, a, b, u, n]);
        d.lam_fv(n_fv, nat, body)
    };
    let one_nat = d.num(1);
    let k = d.num(3);
    let estimate = d.lemma(p.sup_seq_abs_diff_le, &[f, a, b, u, hab]);
    let raw = d.lemma(
        p.scaled_cauchy_of_abs_diff_le,
        &[f_lambda, one_nat, estimate],
    );
    let proof = d.lemma(p.converges_of_scaled_cauchy, &[f_lambda, k, raw]);

    let target = d.const_app(p.sup_on, &[f, a, b, hab, u]);
    let concl = d.const_app(p.converges, &[f_lambda, target]);

    let ty = {
        // BOTH binders must be `pi_fv`, not `arrow`: the conclusion mentions
        // `u` (through `supSeq`) and `hab` (through `supOn`'s own explicit
        // argument), so a non-dependent arrow leaves them free and the kernel
        // reports only `UnboundFVar`, naming neither.
        let after_u = d.pi_fv(u_fv, u_ty, concl);
        let after_hab = d.pi_fv(hab_fv, hab_ty, after_u);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, func_ty, over_a)
    };
    let value = {
        let with_u = d.lam_fv(u_fv, u_ty, proof);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, func_ty, over_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_seq_converges_sup_on,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.supOn` and `CReal.supSeq_converges_supOn`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sup_on(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_sup_on_def(d, p)?;
    declare_sup_seq_converges_thm(d, p)
}
