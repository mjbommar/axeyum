//! **`CReal.riemannSum`** — the first integral in this kernel: a finite
//! left-endpoint Riemann sum over `[a, b]` with `Nat.succ m` equal
//! subintervals, built directly on [`super::series`]'s `CReal.sumRange`.
//!
//! ## Why this is a plain `Definition`, not a carrier like `HasDerivativeOn`
//!
//! `derivative.rs`'s `HasDerivativeOn` needs a `Type`-valued carrier because
//! its modulus is genuinely *chosen* data attached to an otherwise-`Prop`
//! obligation (see that file's own module documentation). A Riemann sum has
//! no such data to carry: for a fixed `f`, `a`, `b` and subinterval count, the
//! sum is one fully-determined `CReal`, computed the same way `CReal.sumRange`
//! itself is — so it is a `Definition` built directly out of `add`, `neg`,
//! `mul`, `ofRat`, `ofNat` and `sumRange`, with no `Prop` anywhere in sight.
//!
//! ## The subinterval count, and why division needed no positivity witness
//!
//! `Δ = (b − a)/n` needs `n ≠ 0`. `CReal.inv` ([`super::inverse`]) exists but
//! takes a `PosBound` witness as an explicit argument — exactly the
//! "positivity witness makes the definition awkward" trap the task briefing
//! warned about, and it *would* be awkward here: threading a proof of
//! `0 < ofNat n` through a **finite**, totally ordinary definition just to
//! divide by a natural number is the wrong tool.
//!
//! It is also unnecessary. `n` is a `Nat`, not a `CReal`, so `1/n` is a
//! **rational** number regardless of `a`/`b`, and `Rat.natDivSucc 1 j := 1/(j+1)`
//! ([`archimedean.rs`](super::archimedean)) is already total in `j`. Taking the
//! subinterval count as `Nat.succ m` — i.e. parametrising `riemannSum` by `m`
//! and reading `n := m + 1` — makes `n ≠ 0` true *by construction* rather than
//! a side condition, and `Δ := (b − a) · ofRat (Rat.natDivSucc 1 m)` is then
//! an ordinary total product, no `CReal.inv`, no `PosBound`, no case split.
//! This is the same trick [`derivative.rs`](super::derivative)'s
//! `hasDerivative_smul` already uses for a *different* division (`|c| ≤ k+1`
//! read as `natDivSucc (Nat.succ k) 0`).
//!
//! ## The sample point: LEFT endpoint
//!
//! `riemannSum f a b m` samples `f` at `a + i·Δ` for `i = 0, …, m` — the
//! **left** endpoint of each subinterval. Left was chosen over the midpoint
//! for exactly the reason the briefing flagged as the trade-off: midpoint
//! gives tighter error bounds for a later convergence proof, but it needs an
//! extra `Δ/2` term in the sample-point arithmetic for no benefit to *this*
//! slice (no error bound is proved here at all — only linearity,
//! monotonicity and the exact constant-function computation). Left endpoint
//! is `a + i·Δ` with no further arithmetic, and it is what makes the mandatory
//! computation test (`riemannSum (fun _ => one) zero one 0`, single
//! subinterval, sample point `zero`) land on the obvious index-`0` case.
//!
//! ## What is proved here
//!
//! - **`riemannSum`** itself.
//! - **`riemannSum_add`**: `riemannSum (f+g) ~ riemannSum f + riemannSum g`,
//!   via [`super::series::CRealPrelude::sum_range_congr`] against
//!   [`right_distrib`] (distributing `Δ` into each term) then
//!   [`super::series::CRealPrelude::sum_range_add`].
//! - **`mul_riemannSum`**: `riemannSum (c·f) ~ c · riemannSum f`, via the same
//!   `sum_range_congr` shape against `mul_assoc` (re-associating `(c·f(x))·Δ`
//!   to `c·(f(x)·Δ)`) then
//!   [`super::series::CRealPrelude::mul_sum_range`].
//! - **`riemannSum_le`**: monotonicity, `le a b → (∀ z, le (f z) (g z)) →
//!   le (riemannSum f a b m) (riemannSum g a b m)`. The hypothesis is
//!   **global** (`∀ z`, not restricted to `[a, b]`). `le a b` is still
//!   genuinely used: it is exactly what makes `Δ ≥ 0`, which
//!   [`CRealPrelude::mul_le_mul_of_nonneg_left`] needs to multiply the
//!   pointwise hypothesis through by `Δ` without reversing it.
//! - **`ofNat_le`**: `Nat.le i j → CReal.le (ofNat i) (ofNat j)` — `CReal.ofNat`
//!   is monotone, via `Nat.le_dest` plus
//!   `RatPrelude::nat_div_succ_le_add_left` lifted across
//!   [`CRealPrelude::of_rat_le`]. Independently reusable; nothing else in the
//!   prelude had it.
//! - **`riemannSum_sample_in_bounds`**: `le a b → i < succ m → a ≤ a + i·Δ ≤
//!   b` — every LEFT-endpoint sample point lies in `[a, b]`. The piece
//!   `riemannSum_le`'s own doc used to flag as missing: nonneg-ness of the
//!   lower half ([`shift_le_of_nonneg`], generalizing
//!   [`CRealPrelude::le_add_of_nonneg`] off the rational embedding) and
//!   `ofNat_le` composed with `mul_le_mul_of_nonneg_left` plus the exact
//!   identity `n·Δ ~ (b−a)` ([`mesh_times_count_eq_width`], reusing
//!   [`mesh_inverse_identity`]) for the upper half.
//! - **`riemannSum_le_on`**: `riemannSum_le` with the pointwise hypothesis
//!   RESTRICTED to `[a, b]` (`∀ z, le a z → le z b → le (f z) (g z)`), via
//!   `riemannSum_sample_in_bounds`. `riemannSum_le` itself is **unchanged** —
//!   both theorems exist, stated exactly as their own doc comments say.
//!
//! - **`riemannSum_const`**: `riemannSum (fun _ => c) a b m ~ c · (b − a)`,
//!   exactly, for every `m` — the theorem that says the definition is right
//!   (a constant function's integral is base times height, with no error
//!   term, whatever the subinterval count). Two independent pieces:
//!
//!   1. [`riemann_sum_const_core`]: `sumRange (fun _ => w) (succ m) ~ mul
//!      (ofNat (succ m)) w`, a plain sum-of-a-constant induction on `m`. The
//!      base case needs `ofNat 1 ~ one` ([`of_nat_one_equiv_local`]); the
//!      step needs `ofNat (succ k) ~ add (ofNat k) one`
//!      ([`of_nat_succ_equiv_local`]) plus [`right_distrib`]. Both `of_nat_*`
//!      helpers are local restatements of `derivative.rs`'s private
//!      `of_nat_one_equiv`/`of_nat_succ_equiv` (that file is out of scope for
//!      this slice, so this module cannot call them, only rebuild the same
//!      two short proofs).
//!   2. [`mesh_inverse_identity`]: `mul (ofNat (Nat.succ m)) (embed
//!      (Rat.natDivSucc 1 m)) ~ one` — exactly the `(m+1)/(m+1) = 1` identity
//!      `RatPrelude::inv_nat_div_succ`'s own proof derives in passing
//!      (chaining `nat_div_succ_mul`, `nat_div_succ_scale` and the
//!      already-proved `CReal.ratUnitEqOne` in place of a fresh
//!      `self_normalize` call — see
//!      `rat_prelude/field.rs::declare_inv_nat_div_succ` and
//!      [`nat_div_succ_inverse_pair_eq_one`]), lifted from `Rat` to `CReal`
//!      by `CReal.ofRat_mul`.
//!
//!   [`declare_riemann_sum_const`] combines the two: the summand
//!   `f(a+i·Δ)·Δ` is `c·Δ` regardless of `i` since `f` is constant (an
//!   ordinary beta reduction the kernel's defeq check performs on its own,
//!   so [`riemann_sum_const_core`] is stated and used directly against
//!   `w := mul c delta` with no bridging lemma needed), piece 1 collapses the
//!   sum to `mul (ofNat n) (mul c delta)`, and an eight-step
//!   associativity/commutativity rewrite (using `mul_assoc`/`mul_comm`/
//!   `mul_congr`) exposes `mul (ofNat n) frac_real` next to the width so
//!   piece 2 cancels it, leaving `mul c width` via `mul_one`.
//!
//! **Not attempted**: additivity over an interval split (`riemannSum f a c`
//! vs. `riemannSum f a b` plus `riemannSum f b c`), which is false for a
//! FIXED subinterval count unless the two partitions happen to line up — see
//! `declare_integral`'s caller for that check.
//!
//! ## `CReal.integral_split` — checked 2026-08-26, blocked, with the
//! `riemannSum` counterexample this doc had only asserted
//!
//! Task: settle whether `CReal.integral_split : ∀ F a b c hab hac hcb u uac
//! ucb, le a c → le c b → Equiv (integral F a b hab u) (add (integral F a c
//! hac uac) (integral F c b hcb ucb))` is (1) false at the `riemannSum`
//! level, (2) true and provable for `integral`, or (3) blocked on the same
//! witness-comparison wall found the same day to block `integral_add` /
//! `integral_scale` / `integral_le`. **Answer: (1) is confirmed by an exact
//! counterexample, and (3) holds for `integral` itself — nothing was added.**
//!
//! **(1), the `riemannSum` counterexample**, exact rational arithmetic, no
//! kernel needed: at `m = 0` (`n = 1` subinterval, `Δ = b − a`,
//! `riemannSum f a b 0 = f(a)·(b − a)`), take `f := id`, `a := 0`, `c := 1`,
//! `b := 3`. Then `riemannSum id 0 3 0 = 0·3 = 0`, while `riemannSum id 0 1 0
//! = 0·1 = 0` and `riemannSum id 1 3 0 = 1·2 = 2`, so the parts sum to `2 ≠
//! 0`. The doc paragraph above was right; this pins it to a checkable
//! instance.
//!
//! **(3), why `integral_split` itself is blocked, precisely**: every
//! `Equiv`/`Converges` bridge this file has (`declare_integral_const` is the
//! template) goes through `CReal.converges_unique : ∀ f L M, Converges f L →
//! Converges f M → Equiv L M` — both `Converges` facts must name the
//! **syntactically same** sequence `f`. `integral F a b hab u`'s own
//! sequence is `f_lambda_ab n := riemannSum F a b (deep F a b u n + 0)`
//! ([`integral_witness`]), tied to `u`'s own modulus. `integral_split`
//! states three INDEPENDENT witnesses `u`, `uac`, `ucb`, so
//! `CReal.converges_add` gives `Converges (fun n => add (f_lambda_ac n)
//! (f_lambda_cb n)) (add (integral F a c hac uac) (integral F c b hcb
//! ucb))`, but that sequence is a different one from `f_lambda_ab`, and
//! `converges_unique` cannot compare across two different sequences that
//! merely converge to related values. Closing the gap needs either a
//! Riemann-sum-vs-true-value estimate through a modulus of continuity (the
//! same thing the paragraph above already named as missing — bounding how
//! far `riemannSum F a b m` sits from the limit, independent of which
//! witness produced `m`), or a direct proof that `CReal.integral`'s VALUE
//! does not depend on the choice of `UniformlyContinuousOn` witness. Neither
//! exists in this prelude; **this is one gap, not two** — a witness-
//! independence proof would itself be built from exactly such an estimate.
//!
//! `CReal.sumRange_split` (`series.rs`) does NOT dissolve this: it splits a
//! sum over `Nat.add m n` INDICES into a sum over `m` plus a shifted sum over
//! `n` — a fact about one fixed sequence's own index range, not about two
//! `riemannSum`s built from different intervals and different moduli. It
//! could only feed a split proof if `c` were forced to land exactly on a
//! shared partition's grid point, which the general statement (arbitrary
//! `c`, arbitrary independent `uac`/`ucb`) does not give.
//!
//! Checked against `prelude_theorem_inventory --include-constructed --release`
//! (2026-08-26): no `riemannSum_split`, `integral_split`, `integral_add`, or
//! any modulus-/witness-independence lemma existed anywhere in the `creal`
//! prelude at that time; `sumRange_split` and `riemannSum_const` (the
//! positive control) were both present as named above. `integral_add`,
//! `integral_le`, `integral_scale` and `integral_witness_independent` landed
//! shortly after (this file's own history), and
//! [`CRealPrelude::riemann_sum_integral_close`] (`declare_riemann_sum_integral_close`,
//! this file) now supplies the Riemann-sum-vs-true-value estimate itself:
//! for ANY fixed mesh `m := deep(e) + depth` at least as deep as accuracy
//! `e`'s Archimedean threshold, `riemannSum F a b m` sits within an
//! explicit, `e`-derived distance of `CReal.integral F a b hab u`, built by
//! chaining `riemannSum_shared_accuracy_close` (fixed mesh vs `f_lambda e`)
//! with `speedup_close` (`f_lambda e` vs the integral's own sample at `e`,
//! reconstructing `integral_witness`'s triple rather than going through
//! `integral_converges`'s `Exists`-wrapped `Converges`, which hides the rate
//! this estimate needs to NAME).
//!
//! **`integral_split` itself is still open.** The estimate above compares
//! ONE `riemannSum F a b m` to ITS OWN interval's integral; `integral_split`
//! needs to compare `riemannSum F a b m` (over `[a,b]`) against a SUM of two
//! Riemann sums over `[a,c]`/`[c,b]` built at generally different, refined
//! mesh counts — a genuinely new bridging step (splitting `m`'s own sample
//! points at `c`, relating the split sub-sums back to `riemannSum F a c
//! m_ac`/`riemannSum F c b m_cb` at SOME refined `m_ac`/`m_cb`) that this
//! estimate is the prerequisite for, not a proof of. Next open goal,
//! precisely: that mesh-splitting bridge, using
//! `riemann_sum_integral_close` (this file) on all three intervals once
//! it exists.
//!
//! ## `CReal.integral_split` — checked 2026-08-27, still blocked; the
//! remaining gap is structurally different from every other cross-object
//! bridge this file has, and here is precisely why
//!
//! Task: attempt the mesh-splitting bridge the 2026-08-26 entry names.
//! **Not built.** Two findings, one positive (a real simplification for
//! whoever attempts this next) and one negative (why the attempt still does
//! not close):
//!
//! **Positive: the "same sequence" objection in the 2026-08-26 entry is
//! avoidable, and does not need to be solved.** That entry's point (3)
//! argued `converges_unique` needs the two `Converges` facts to name the
//! syntactically same sequence, which three independent witnesses `u`,
//! `uac`, `ucb` do not give. `CReal.le_of_forall_le_add_small` / its wrapper
//! `CReal.equiv_zero_of_small` (`creal/archimedean_squeeze.rs`, already in
//! the prelude, callable from here) sidestep this entirely: `equiv_zero_of_small
//! : ∀ v, (∀ e, le (abs v) (ofRat (natDivSucc 1 e))) → Equiv v zero` proves an
//! `Equiv` from an arbitrary-accuracy **rational** bound on one difference,
//! with no shared underlying sequence required at all. Applied to `v :=
//! integral F a b hab u − (integral F a c hac uac + integral F c b hcb
//! ucb)`, this is the right tool to FINISH the proof once the per-`e` bound
//! exists. It is not, itself, that bound.
//!
//! **Negative, and this is the actual remaining gap: producing that per-`e`
//! bound needs a term-by-term comparison between Riemann sums over
//! DIFFERENT, generally incommensurate-width intervals, and nothing in this
//! file's arithmetic toolkit does that.** Every "combine several riemannSums"
//! construction that already exists here — `common_refinement`,
//! `common_refinement3`, `sharedIndexToCanonical`,
//! `riemannSumDeepCauchyCross`, `riemannSumAddCauchyCross`, `sumRange_split`,
//! `fineBlockSum_close`, and the whole `sumRange_reblock` family underneath
//! `riemann_sum_integral_close` itself — compares riemann sums over the
//! **same interval** `[a, b]` at different mesh counts (refining `m` to a
//! common multiple `l`), or the same interval/mesh at a different function or
//! different continuity witness. Every one of those refinements is a PURE
//! `Nat` computation: `mesh_reciprocal_mul`/`succ_mul_succ` show a refined
//! step `(b−a)/(l+1)` is an EXACT algebraic multiple of the coarse step
//! `(b−a)/(m+1)`, so no comparison between two different CReal widths is
//! ever needed — only `Nat.mul`/`Nat.add` identities.
//!
//! `[a, c]` and `[c, b]` are different intervals from `[a, b]`, with widths
//! `c − a` and `b − c` that are, for an arbitrary `CReal c` with `a ≤ c ≤ b`,
//! **not** rational multiples of `b − a`, and not computably comparable to it
//! at all (CReal apartness/order is not decidable). So there is no Nat count
//! `m_ac`/`m_cb` whose step size `(c−a)/(m_ac+1)` / `(b−c)/(m_cb+1)` can be
//! made to EQUAL `(b−a)/(m_ab+1)` by the `common_refinement`-style algebra —
//! confirmed by trying: `common_refinement`/`common_refinement3` both take
//! their two or three `Nat` counts over a SINGLE shared interval as a
//! precondition baked into their construction (`succ_mul_succ` multiplies
//! `Nat` counts, never touches a `CReal` width), and neither has, nor can be
//! made to have by rearranging their existing calls, a step that relates a
//! count on `[a, c]` to a count on `[a, b]`.
//!
//! A correct proof needs machinery this development does not have on either
//! side of the arithmetic: (1) an Archimedean "crossing index" fact — given
//! the coarse step `Δ_ab := (b−a)/(m_ab+1)` and `c` with `a ≤ c ≤ b`, a `Nat`
//! `i0` such that `a + i0·Δ_ab` is within one step of `c` (existence alone is
//! already delicate: `CReal` order is not decidable, so `i0` cannot be found
//! by comparing `a + i·Δ_ab` against `c` one `i` at a time and stopping — the
//! stopping test is not decidable); and (2) a term-by-term bound on the
//! difference between the partial sum over the crossing block's indices
//! (built from `Δ_ab`, hence sampling slightly outside `[a, c]`) and
//! `riemannSum F a c m_ac` for a comparably-fine `m_ac` (built from the
//! genuinely different step `Δ_ac`), via `F`'s uniform continuity — structurally
//! close to what `pointwise_block_equiv`/`sample_point_reblock_proof` do for
//! a SAME-interval refinement, but neither is stated for two different
//! interval endpoints and neither reduces to the other by substitution
//! (`sample_point_reblock_proof`'s own mesh identity is proved via
//! `mesh_reblock_delta_eq`, which is `Nat`-refinement algebra over ONE
//! `(a, b)` pair, not a fact relating a `[a,b]`-step to an `[a,c]`-step).
//!
//! Neither (1) nor (2) exists anywhere in `creal/` as checked against
//! `prelude_theorem_inventory --include-constructed --release` (2026-08-27,
//! 916 `CReal.*` rows, `riemannSum_integral_close` present as the positive
//! control, `integral_split` absent as expected). Building them is a new
//! sub-development on the scale of the `sumRange_reblock`/
//! `riemann_sum_reblock_close`/`riemann_sum_shared_accuracy_close` chain this
//! file already carries for the single-interval case (roughly 2,500 lines,
//! `declare_riemann_sum` through `declare_riemann_sum_integral_close`) — not
//! a composition of what is already here. **Next open goal, precisely:**
//! build (1), the Archimedean crossing-index fact for `CReal`, first and
//! independently (it is reusable outside this file and does not mention
//! `riemannSum` at all), then (2), the cross-width term comparison, before
//! attempting `integral_split` itself again.
//!
//! No declaration was added by this entry. Nothing above is a kernel
//! rejection — the construction was not attempted at the term level because
//! the two prerequisite facts it would need to cite do not exist to cite.
//!
//! ## `CReal.integral_split` — checked 2026-08-27 (later the same day), fact
//! (1) above landed as [`super::crossing::declare_crossing_close`]
//!
//! A second lane landed [`super::CRealPrelude::crossing_index`] /
//! `crossingUpper` / `crossingLower` / `crossingSampleUpper` /
//! `crossingSampleLower` in `creal/crossing.rs` — the Archimedean
//! crossing-index fact (1) the entry above named as the first prerequisite,
//! reusable outside this file and mentioning no `riemannSum`. This entry
//! landed one bounded slice of (2), the cross-width term comparison: **the
//! single-block bound**, [`super::CRealPrelude::crossing_close`] —
//! `|F(c) − F(sample_point a Δ (crossingIndex a c Δ))| ≤ 1/(e+1)`, via
//! `crossingSampleUpper`/`crossingSampleLower` (two one-sided bounds, moved
//! across the `≤` by two small new local order lemmas,
//! `crossing.rs::le_sub_of_le_add`/`le_sub_of_add_le_left`) combined by
//! `CReal.abs_le` into exactly `UniformlyContinuousOn.spec`'s own hypothesis
//! shape.
//!
//! **`crossing_close` takes two facts as explicit hypotheses rather than
//! deriving them, and both are genuinely separate, not-yet-attempted
//! sub-developments — not simplifications of what it proves:**
//!
//! 1. The Archimedean smallness of the two crossing slacks (`≈2Δ`, `≈1.5Δ`)
//!    relative to `UniformlyContinuousOn`'s modulus at the target accuracy —
//!    this needs a SCALED analogue of [`declare_mesh_le_of_ge`] (which
//!    bounds a mesh step `Δ_m` itself by `1/(n+1)` for `m` past a threshold,
//!    never a small constant MULTIPLE of `Δ_m`), applied to whichever mesh
//!    count produces `Δ := Δ_ab` in the caller's actual setting.
//! 2. `samplePt`'s own domain membership (`a ≤ samplePt ≤ b`) — needs
//!    bounding `crossingIndex` against a mesh count `m` (i.e. `crossingIndex
//!    a c Δ_ab ≤ m` when `Δ_ab := (b−a)/(m+1)`), which `crossing.rs` does
//!    not attempt (it is deliberately interval-count-agnostic — see that
//!    file's own module documentation on where it generalizes).
//!
//! Once both exist for a caller's concrete `a, b, m_ab` setting,
//! `crossing_close` gives EXACTLY the per-block estimate `integral_split`
//! needs for the crossing block's boundary sample; the roadmap step after
//! that (unattempted here) is summing an analogous bound across every index
//! in the crossing block via `sumRange`/`sum_range_le`-style machinery, as
//! the task briefing for this lane named as the (optional) second slice.
//! `creal_prelude_builds` unaffected (~20 s before and after — `Δ` stays a
//! free `Rat` fvar throughout `crossing_close`, never a mesh-derived
//! `Nat.mul`/`Nat.add` term, so none of the concrete-witness/lazy-delta
//! traps this file's own history warns about apply here).
//!
//! ## `CReal.integral_split` — checked 2026-08-27 (later still), a THIRD
//! lane: prerequisite (1) landed as [`CRealPrelude::mesh_scaled_le_of_ge`],
//! prerequisite (2) NOT attempted, and here is exactly why
//!
//! [`declare_mesh_scaled_le_of_ge`] proves the SCALED analogue prerequisite
//! (1) names: `le (mul (ofNat k) Δ_m) (ofRat (natDivSucc 1 outer))` for an
//! explicit Nat multiplier `k := Nat.succ k0`, by reusing
//! [`declare_mesh_le_of_ge`] wholesale at a substituted `outer' := k*outer +
//! k0` and collapsing `k·(1/(outer'+1))` back to `1/(outer+1)` with the same
//! `magnitude_times_frac_eq_outer` helper `mesh_le_of_ge` itself uses (its
//! `(c, magnitude, deep)` slots taking `(k0, k, outer')`, which is EXACTLY
//! `Rat.natDivSucc_scale`'s required syntactic shape). Reusable well beyond
//! this file, and a complete result on its own, independent of everything
//! below.
//!
//! Prerequisite (2) — `samplePt`'s domain membership — was investigated and
//! NOT attempted, because the investigation surfaced a genuine type
//! mismatch prerequisite (2)'s own one-line gloss papers over. `crossing.rs`
//! types `Δ` as a **`Rat`** (`crossingIndex a c Δ`, `Δ : Rat`, invertible via
//! the DECIDABLE `Rat.inv`), while `mesh_le_of_ge`/`mesh_scaled_le_of_ge`'s
//! own mesh step `Δ_m := (b−a)·natDivSucc(1,m)` is a **`CReal`** (`b−a` is an
//! arbitrary real, not generally rational). "`Δ_ab := (b−a)/(m+1)`" — this
//! entry's own predecessor's gloss, repeated in [`CRealPrelude::crossing_close`]'s
//! doc comment — is not literally well-typed as `crossingIndex`'s argument;
//! at best it names a **rational upper bound** for the true real mesh step
//! (e.g. `Δ := natDivSucc(magnitude, m)` for `magnitude := bound(b−a)+1`,
//! since `b−a ≤ ofNat(magnitude)` makes `(b−a)/(m+1) ≤ magnitude/(m+1)`).
//!
//! Working through THAT reading to its end does not land prerequisite (2)
//! either. With `w := (c−a)·Δ⁻¹` (`crossingIndex`'s own rescaled argument),
//! `0 ≤ c−a ≤ b−a ≤ ofNat(magnitude)` and `Δ⁻¹ = ofNat(m+1)/magnitude`
//! (exactly, since `Δ = magnitude/(m+1)`) give `w ≤ ofNat(m+1)` — clean, and
//! [`CRealPrelude::bucket_index_bound`] (`creal/uniform_continuity.rs`,
//! already proved) would then bound `crossingIndex a c Δ = bucketIndex w 0 ≤
//! (bound(ofNat(m+1))+3)*1`, roughly `m+4`, NOT `≤ m`. That gap alone is
//! absorbable (widen the target interval's own slack). The genuinely
//! disqualifying direction is the OTHER one: this `Δ` is an upper bound for
//! the true step, so it can UNDERSHOOT the number of steps actually needed
//! to cross `[a, c]` at accuracy comparable to `Δ`'s own denominator, and
//! nothing above bounds `crossingIndex` in terms of `m` alone without ALSO
//! bounding `magnitude := bound(b−a)+1` — which is data about the interval,
//! not about `m` — so "a caller supplying only a mesh count" cannot be made
//! literally true for THIS reading of `Δ` either. Resolving prerequisite
//! (2) needs a considered choice of what `Δ` actually denotes for
//! `integral_split`'s crossing block (a `Rat` derived from `m` and the
//! interval's own Archimedean bound, per above, OR a different bracketing
//! that avoids `crossingIndex`'s `Rat`-typed step altogether) before further
//! proof engineering is worth attempting — a design question, not a proof
//! gap. Left exactly as prerequisite (2) was before this entry:
//! unattempted, hypothesis, explicit.
//!
//! `creal_prelude_builds`: 23.07 s test-run (was ~19.99 s on the previous
//! lane's build; `Δ`/`k`/`k0`/`outer`/`m` all stay free fvars throughout
//! [`declare_mesh_scaled_le_of_ge`], so none of this file's documented
//! concrete-witness/lazy-delta traps apply — the increase is consistent
//! with ordinary machine load, not a construction cost).
//!
//! ## `CReal.integral_split` — checked 2026-08-27 (a FOURTH lane), tested
//! and REFUTED the hypothesis that "`magnitude` is a fixed constant of
//! `[a,b]`" rescues prerequisite (2); the obstruction is not data
//! availability, it is that `bucket_index_bound`'s existing cap is
//! provably too loose BY EXACTLY THE MARGIN THAT MATTERS, for every mesh
//! count
//!
//! The immediately preceding entry's own "genuinely disqualifying
//! direction" reads, correctly interpreted, as an availability claim: `Δ`
//! being an upper bound for the true step "cannot be made literally true
//! for THIS reading of `Δ`... without ALSO bounding `magnitude`... which is
//! data about the interval, not about `m`". That is true as stated, but
//! `integral_split` FIXES the interval `[a,b]` before this lemma is ever
//! invoked, so `magnitude := bound(b−a)+1` is not a free parameter the
//! caller lacks — it is a closed `Nat` term the caller already has in
//! hand, exactly like `a`, `b` themselves. So the question worth actually
//! testing is: does a bound in the PAIR `(m, magnitude)` — not `m` alone —
//! suffice? It does not, and the reason is arithmetic, not a missing
//! input.
//!
//! **The exact chain, with no step hand-waved.** Fix `bnd := ofNat(N+1)`
//! for whatever Nat `N` the caller picks to build `Δ := natDivSucc
//! (magnitude, N)` (i.e. `Δ = magnitude/(N+1)`, `[CRealPrelude::direct_bound_le`]'s
//! own `(c, magnitude, proof)` triple applied to `width := b−a`, so
//! `proof : le (b−a) (ofNat magnitude)` is exactly what is in hand — no
//! stronger, no `<`, a plain `≤`). Then:
//!
//! 1. `w := (c−a)·Δ⁻¹` satisfies `le w bnd`: `Δ⁻¹ = ofNat(N+1)/magnitude`
//!    exactly (both positive, `Rat.inv` of a `natDivSucc`), and `c−a ≤ b−a
//!    ≤ ofNat(magnitude)`, so `w ≤ magnitude·(N+1)/magnitude = ofNat(N+1) =
//!    bnd`.
//! 2. [`CRealPrelude::bucket_index_bound`] at `(w, bnd, k := 0, that
//!    proof)` gives `crossingIndex a c Δ = bucketIndex w 0 ≤ (bound(bnd) +
//!    3)·1`. `bnd = ofNat(N+1)` is itself a `direct_bound_le`-shaped
//!    embedding, and `CReal.bound`'s literal definition
//!    (`product.rs::declare_bound`, `Int.natAbs (Rat.num (seq x 0)) + 1`)
//!    gives `bound (ofNat (N+1)) = N+2` exactly (the 0th sample of a
//!    constant-`Nat` embedding is that Nat as an integer-denominator
//!    rational, numerator `N+1`, `natAbs (N+1) = N+1`). So the cap is
//!    **exactly `N + 5`**, not `N + 1` — a fixed excess of `4`, independent
//!    of `N` and of `magnitude`.
//! 3. Multiply back by `Δ = magnitude/(N+1)`: the PROVABLE bound on
//!    `crossingIndex a c Δ · Δ` (hence on `samplePt − a`) is `(N+5)·
//!    magnitude/(N+1) = magnitude · (1 + 4/(N+1))`. This is **strictly
//!    greater than `magnitude` for every finite `N`** — the `4/(N+1)` term
//!    is always strictly positive, however large `N` is chosen.
//! 4. The only available fact relating `b−a` to `magnitude` is
//!    `direct_bound_le`'s own `le (b−a) (ofNat magnitude)` — non-strict,
//!    and nothing in the prelude proves a strict `lt (b−a) (ofNat
//!    magnitude)` with any quantified gap. So the best available ceiling
//!    on `samplePt − a` needed for `samplePt ≤ b` is `magnitude` itself,
//!    and step 3's provable bound is *always* strictly above that ceiling.
//!
//! **`samplePt ≤ b` is therefore not derivable via `bucket_index_bound` +
//! `direct_bound_le` for ANY choice of the internal parameter `N`** — not
//! "not yet, for small `N`", not "needs `N` past some threshold": the
//! excess `4·magnitude/(N+1)` shrinks toward `0` as `N → ∞`, but the
//! bound it is added to is already pinned at exactly `magnitude`, the same
//! constant the ceiling sits at, so the sum never crosses below it. Refining
//! the mesh makes the bound TIGHTER, never makes it SUFFICIENT. Checked
//! concretely: `magnitude := 10` (i.e. `b−a` bounded by `10`), `N := 10^6`
//! gives a provable cap of `10·(1 + 4/1000001) ≈ 10.00004`, still `> 10 ≥
//! b−a`'s only known ceiling; `N := 10^9` gives `≈ 10.00000004`, same
//! verdict. The gap never closes because it is not a convergence-speed
//! problem, it is that the limit itself (`magnitude`) already sits at the
//! ceiling `b−a` is only known to be `≤`, not `<`, by any provable margin.
//!
//! **So my own working hypothesis for this lane — "since `magnitude` is a
//! determined constant of the fixed interval, a bound in `(m, magnitude)`
//! should suffice" — is REFUTED, but not for the reason the hypothesis
//! disputed.** `magnitude` genuinely IS usable, closed data at a fixed
//! interval; that part of the hypothesis was correct, and the previous
//! entry's framing ("data about the interval, not about `m`") is easy to
//! misread as saying the obstruction is unavailable information. It is not.
//! The actual obstruction is that [`CRealPrelude::bucket_index_bound`] — the
//! ONLY existing `Nat` cap on `bucketIndex`/`crossingIndex` — carries a
//! FIXED additive slack (`+3`, becoming `+4` once composed with `bnd`'s own
//! `+1` embedding offset) that, once multiplied back through `Δ`'s
//! denominator, lands EXACTLY on `magnitude` from above, and `magnitude` is
//! also exactly where `b−a`'s only known ceiling sits. A strictly TIGHTER,
//! purpose-built bound on `crossingIndex` specifically (not the generic
//! clamp-based `bucket_index_bound`, which was designed for `bounded_of_
//! uniformly_continuous`'s covering argument and never promises tightness
//! beyond "some `Nat` cap exists") — one whose slack vanishes relative to
//! `magnitude`, not merely relative to `N` — would be needed before
//! prerequisite (2) is even attemptable at the term level. That is new
//! proof engineering on `crossing.rs`'s own ground, not a matter of
//! supplying `bucket_index_bound` with more inputs, and not attempted here:
//! doing so without first fixing the +4 slack would be building something
//! that only LOOKS like it discharges the hypothesis.
//!
//! No declaration was added or attempted at the term level — the
//! arithmetic above rules out the natural construction before any kernel
//! call, the same discipline the immediately preceding entry followed.
//! `samplePt`'s domain membership remains open; [`CRealPrelude::crossing_close`]
//! is UNCHANGED and still takes it as an explicit hypothesis alongside the
//! Archimedean-smallness one (which IS now dischargeable, via
//! [`CRealPrelude::mesh_scaled_le_of_ge`], per the entry above — that
//! wiring is also not attempted here, since it is orthogonal to this
//! entry's negative finding and better left for whoever next revisits
//! `crossing_close`'s statement as a whole).
//!
//! `creal_prelude_builds`: measured 22.17 s on this lane's merge of `main`
//! + the previous lane's branch, BEFORE this entry (pure prose, no new
//!   declaration) and unaffected by it.
//!
//! ## `CReal.integral_split` — checked 2026-08-27 (a FIFTH lane), a TIGHTER
//! `crossingIndex` bound was searched for, found, and shown to still NOT
//! rescue prerequisite (2) — for a reason ORTHOGONAL to
//! [`CRealPrelude::bucket_index_bound`]'s own `+3`/`+4` slack, not merely a
//! smaller instance of it
//!
//! **Step 0 first: no existing lemma bounds `crossingIndex` any tighter than
//! [`CRealPrelude::bucket_index_bound`] already does** (`prelude_theorem_
//! inventory --include-constructed --release` has no second `bucketIndex`/
//! `crossingIndex` cap, and `integral.rs`'s own `riemannSum_sample_in_bounds`/
//! `subdivisionPoint_in_bounds` solve a DIFFERENT problem — see below). So a
//! tighter bound, if one exists, has to be built, not found.
//!
//! **One does exist, and it is provably tight.** The fourth entry's own cap
//! (`crossingIndex ≤ bound(bnd) + 3`, `bnd := ofNat(N+1)`) comes from
//! [`declare_bucket_index_bound`](super::uniform_continuity)'s GENERIC
//! route: it instantiates `hle : w ≤ bnd` at `bucketIndex`'s OWN sampling
//! accuracy `j = 1` (forced by `k := 0`), then WIDENS the resulting `2/(j+1)
//! = 1` margin up to the worst-case `2` so the proof works for every `k`
//! simultaneously — a real loss when `k` happens to be fixed at `0`, since
//! `2/(1+1)` is not loose at all. Building a proof SPECIFIC to `k = 0`
//! avoids that widening entirely: combine [`CRealPrelude::regular`] (`w`'s
//! own two-index Cauchy bound) at `(1, n')` for a FIXED auxiliary accuracy
//! `n'` with `hle` at `n'` itself (not at `j = 1`):
//!
//! ```text
//! seq_w(1)  ≤  seq_w(n') + 1/2 + 1/(n'+1)              [w's own regularity]
//! seq_w(n') ≤  seq_bnd(n') + 2/(n'+1)                   [hle at n', not j]
//! seq_bnd(n') = N+1 exactly                             [bnd = ofNat(N+1), constant]
//! ⟹ seq_w(1) ≤ (N+1) + 1/2 + 3/(n'+1)
//! ```
//!
//! Any fixed `n' ≥ 6` makes `3/(n'+1) < 1/2`, so `seq_w(1) < (N+1) + 1 =
//! N+2`, giving `crossingIndex = ⌊max(seq_w(1), 0)⌋ ≤ N+1` — **exactly the
//! natural ceiling on `w` itself, zero excess**, beating the generic route's
//! `N+5` by the full `+4`. Concretely checked against the two existing
//! instantiations (`a:=0, Δ:=1, c:=5/2 ⟹ crossingIndex=2`, `c:=7/2 ⟹ 3`):
//! both are literal `ofRat` constants, so `seq_w(1) = w` exactly (no
//! approximation to bound at all) and the tightened cap is trivially
//! satisfied with room to spare, exactly as it must be for a valid upper
//! bound — the slack this construction removes only bites for a `c` that is
//! NOT a bare rational literal, which is the general case `crossingClose`
//! actually needs.
//!
//! **This zero-excess bound still does not make `samplePt ≤ b` provable,
//! and the reason is independent of `crossingIndex`/`bucketIndex` entirely:
//! `CReal.bound` is a strict, non-tight over-estimate BY DESIGN, and both
//! available routes to `samplePt ≤ b` go through it (or an equivalent
//! closeness slack) at a point that cannot be tightened away.**
//!
//! Route A (the mesh-count route, refined): `samplePt − a = crossingIndex·Δ
//! ≤ (N+1)·Δ = (N+1)·magnitude/(N+1) = magnitude` — now EXACT, no residual
//! `+4/(N+1)` term at all. But the goal is `samplePt − a ≤ b − a`, and the
//! ONLY available relation between `magnitude` and `b−a` is
//! [`direct_bound_le`]'s `b − a ≤ magnitude` — non-strict, and, per
//! `CReal.bound`'s own definition (`archimedean.rs`'s `bound_of`:
//! `natAbs(num(seq x 0)) + 1`, then `direct_bound_le` adds ANOTHER `+1` on
//! top to form `magnitude`), GENERICALLY STRICT by a FIXED gap unrelated to
//! `N`. Checked concretely: for `x` a literal `ofRat(1)` (so `bound(1) =
//! natAbs(1)+1 = 2`), `magnitude = bound(1)+1 = 3` — three times the true
//! width `1`, for the simplest possible input, and this gap is computed
//! ONCE, before any mesh or crossing-index reasoning starts, so refining `N`
//! cannot shrink it. `samplePt − a ≤ magnitude` and `b − a ≤ magnitude` are
//! both true and say nothing about each other: `magnitude` sits at or above
//! BOTH quantities, and `samplePt − a` reaching all the way up to
//! `magnitude` (which the zero-excess bound shows IS achievable at the
//! mesh's coarsest cell) can genuinely exceed `b − a` when `magnitude > b −
//! a`, which is the typical case, not a corner one. **The obstruction the
//! fourth entry found is not `bucket_index_bound`'s slack — it is that
//! `CReal.bound` supplies an over-estimate with no matching lower bound, so
//! ANY mesh built from it inherits a gap no amount of `crossingIndex`
//! tightening touches.** There is no alternative "get a Nat ceiling out of a
//! `CReal`" primitive in this prelude to route around it (checked: the only
//! candidates are `bound`/`bound_within`/`direct_bound_le`, all the same
//! over-estimate by construction).
//!
//! Route B (direct, no `bnd`/`magnitude` at all):
//! [`CRealPrelude::crossing_sample_lower`] already gives, unconditionally on
//! any tightening here, `samplePt ≤ c + 1.5Δ` (`crossingLower`'s own `3/(j+1)
//! = 1.5` slack at `j=1`). With `c ≤ b`, that is `samplePt ≤ b + 1.5Δ` — off
//! by exactly the CLOSENESS slack the crossing-index module documentation
//! already names as fixed and explicitly out of scope to tighten (`creal/
//! crossing.rs`: "`≤2Δ` above, `≤1.5Δ` below... this is the exact pair of
//! bounds this file can actually build"). For `c = b` exactly (permitted:
//! only `c ≤ b`, not `c < b`, is hypothesised), no choice of `Δ > 0` closes
//! this gap.
//!
//! **So the negative is now sharper than the fourth entry's**: it is not
//! that `bucket_index_bound`'s specific cap is too loose (a defect that
//! COULD, in principle, be a proof-engineering gap to close) — a
//! purpose-built, zero-excess replacement for it was built in this entry's
//! reasoning and it STILL fails, via a second, independent obstruction
//! (`CReal.bound`'s inherent non-tightness) that no `crossingIndex`-side
//! bound can touch, plus a THIRD, already-acknowledged one (Route B's fixed
//! `1.5Δ`) that does not even mention `bucket_index_bound`. Landing the
//! zero-excess bound as a standalone lemma was considered and DECLINED: it
//! would be real (the construction above type-checks against every
//! ingredient's actual signature — `CRealPrelude::regular`, `crossing_lower`'s
//! own `hle`-at-`j` pattern, `Rat.le_of_sub_le`), but it does not unblock
//! `samplePt ≤ b` or anything downstream, so it would be exactly the "proof
//! engineering that only looks like it discharges the hypothesis" the fourth
//! entry already declined to build. No kernel declaration was attempted for
//! either the tighter bound or `samplePt ≤ b`.
//!
//! **What WAS landed this entry, because it needs neither of the two
//! obstructions above:** [`CRealPrelude::crossing_sample_ge_a`]
//! (`creal/crossing.rs`) — the OTHER half of `crossingClose`'s domain-
//! membership pair, `a ≤ samplePt`, needing only `0 < Δ`. `crossingIndex`
//! embeds as a nonnegative `Nat` regardless of `c`'s position and `Δ > 0`
//! makes the product nonnegative too (`CReal.mul_nonneg`), exactly the shape
//! `riemannSum_sample_in_bounds`'s own lower half already proves for an
//! ordinary mesh sample (`zero_le_of_nat`/`shift_le_of_nonneg`, copied
//! locally into `crossing.rs` per this file's own per-module-helper
//! convention). `crossingClose`'s hypothesis list is reduced by exactly one;
//! `samplePt ≤ b` remains the sole open domain-membership premise, and per
//! this entry's arithmetic, it is not reachable by tightening
//! `crossingIndex`'s bound however far — a genuinely different obstruction
//! (in `CReal.bound` itself, or in the acknowledged-fixed `1.5Δ` closeness
//! slack) would need to be resolved first, and neither is `crossing.rs`'s or
//! `integral.rs`'s own ground to break: `CReal.bound`'s tightness is a
//! `product.rs`/`archimedean.rs` question, and the `1.5Δ` slack is
//! `bucketIndex`'s own undecidable-comparison floor, out of scope by this
//! task's own instruction.
//!
//! `creal_prelude_builds`: 21.47 s (this lane's merge of `main` + the fourth
//! lane's branch, WITH `crossingSampleGeA` landed) — no regression from the
//! ~22.17 s / ~19.99 s baseline the fourth/third entries already flagged as
//! noise-dominated.
//!
//! ## `CReal.integral_split` — checked 2026-08-27 (a SEVENTH lane), dispatched
//! to ASSEMBLE the theorem from [`super::crossing::declare_crossing_close_clamped`],
//! [`declare_mesh_scaled_le_of_ge`] and [`declare_riemann_sum_integral_close`].
//! **Still blocked, and the reason is a different SHAPE of gap than any of
//! the six entries above individually name, though it is the same gap the
//! third entry's own final paragraph and `derivative.rs`'s
//! `hasDerivative_integral_const` doc comment both already point at.**
//!
//! The dispatch briefing's proposed shape was: fix `e`; pick mesh depths on
//! all three intervals via [`declare_riemann_sum_integral_close`]; "relate the
//! `[a,b]` sum to the two sub-sums using the crossing machinery — the
//! crossing block's error bounded by `crossingCloseClamped` +
//! `meshScaledLeOfGe`, the interior blocks by the existing single-interval
//! reblock algebra"; close with
//! [`super::archimedean_squeeze::CRealPrelude::equiv_zero_of_small`]. Worked
//! through at the level of what each piece actually STATES, not just what it
//! is named for, before any kernel call:
//!
//! **What `crossingCloseClamped` (with its two remaining hypotheses
//! discharged via `meshScaledLeOfGe`, which is a real, buildable, ~15-call
//! wiring — the two slack terms are `Δ·(1+bound2j)` and `Δ·(neg bound3j)` for
//! FIXED `bound2j = 1`, `bound3j = 3/2` at this file's own `j := 1`, so
//! `slack_upper ≡ ofNat 2 · Δ` and `neg slack_lower ≡ ofNat 2 · Δ` after the
//! same `of_nat_one_equiv_local`/`of_nat_succ_equiv_local`/`right_distrib`
//! moves [`riemann_sum_const_core`] already uses, letting ONE
//! `mesh_scaled_le_of_ge` instance at `k0 := 1` cover both) actually gives is
//! a bound on `abs (F c - F clampedPt)` for **one single sample point** —
//! `clampedPt`, the coarse `[a,b]`-mesh's OWN crossing-index sample, clamped
//! into range.
//!
//! **What `riemannSum F a b m_ab` needs, to be related to `riemannSum F a c
//! m_ac + riemannSum F c b m_cb`, is a bound on the discrepancy between TWO
//! WHOLE SUMS**: `sumRange (fun i => F(a+iΔ_ab)·Δ_ab) (m_ab+1)` against
//! `sumRange (fun j => F(a+jΔ_ac)·Δ_ac) (m_ac+1) + sumRange (fun k =>
//! F(c+kΔ_cb)·Δ_cb) (m_cb+1)`. Bounding a SUM by bounding one term of it
//! (the crossing term) says nothing about the other `m_ab` terms UNLESS they
//! can be shown to correspond, index-for-index, to terms of the `[a,c]`/
//! `[c,b]` sums — which needs each `[a,b]`-mesh sample point BEFORE the
//! crossing index to be within `F`'s modulus of SOME `[a,c]`-mesh sample
//! point, for every one of up to `m_ab` indices simultaneously, not just at
//! the boundary. **This is exactly the "existing single-interval reblock
//! algebra" the briefing proposed reusing for "the interior blocks" — and it
//! does not apply here**: every reblock/common_refinement construction in
//! this file (`common_refinement`, `common_refinement3`,
//! `sharedIndexToCanonical`, the whole `sumRange_reblock` chain) relates two
//! meshes on the SAME interval `[a,b]` (a refined step is an EXACT algebraic
//! multiple of the coarse one, `mesh_reciprocal_mul`/`succ_mul_succ`, pure
//! `Nat` arithmetic). `Δ_ab := (b-a)/(m_ab+1)` and `Δ_ac := (c-a)/(m_ac+1)`
//! are steps of DIFFERENT, generally incommensurate widths (`c-a` is not a
//! computable rational multiple of `b-a` for an arbitrary `CReal c`), so no
//! choice of `m_ac` makes an `[a,c]`-mesh sample point EXACTLY coincide with
//! an `[a,b]`-mesh sample point — the "interior blocks" have no existing
//! algebra to reuse at all, not even approximately, without a NEW
//! cross-width correspondence between the two grids.
//!
//! So even with a fully-wired `crossingCloseClamped` in hand, the assembly
//! stops at the exact same place `crossing.rs`'s own module documentation
//! ("landed here as a standalone, reusable fact rather than wired into
//! `CReal.integral_split`, which needs a SECOND, LARGER fact") and this
//! file's third 2026-08-27 entry ("a term-by-term bound on the difference
//! between the partial sum over the crossing block's indices... and
//! `riemannSum F a c m_ac`... structurally close to what
//! `pointwise_block_equiv`/`sample_point_reblock_proof` do for a SAME-interval
//! refinement, but neither is stated for two different interval endpoints")
//! already named. `crossingCloseClamped` closed exactly the two hypotheses
//! those entries flagged as open on the SINGLE-POINT bound; it does not
//! (and was never claimed to) extend that bound across a whole block of
//! indices.
//!
//! **Independent corroboration, not previously cross-referenced from this
//! file:** `derivative.rs`'s own `declare_has_derivative_integral_const`
//! section comment states plainly that the general (non-constant) case of
//! Spivak Ch14's Fundamental Theorem "needs additivity of `integral` over a
//! split point plus a Riemann-sum-vs-`F(x)*(y-x)` estimate — neither built
//! anywhere in this prelude yet" — written independently of this file's own
//! `integral_split` entries, about the SAME missing "additivity over a
//! split" fact, from the consumer side.
//!
//! **No kernel declaration was attempted.** The gap is structural (a
//! whole-sum comparison across differently-scaled meshes, not a hypothesis
//! this file's existing lemmas can discharge), so — per this task's own
//! instruction to name a genuinely missing piece rather than build something
//! that only looks like it discharges it — nothing was written at the term
//! level. **Precisely what is still needed, unchanged in kind from the third
//! entry's own conclusion but now confirmed against the fully-landed
//! prerequisites**: a lemma bounding `abs (riemannSum F a b m_ab -
//! (riemannSum F a c m_ac + riemannSum F c b m_cb))` for a SUITABLE CHOICE of
//! `m_ac`/`m_cb` given `m_ab` (or vice versa), via `F`'s uniform continuity
//! applied ACROSS the crossing block's full index range (not just at
//! `crossingIndex` itself) — a new sub-development on the same order as the
//! `riemannSum`→`riemannSum_integral_close` chain this file already carries
//! (~2,500 lines), not a composition of `crossingCloseClamped` +
//! `meshScaledLeOfGe` + `riemannSumIntegralClose` +
//! `le_of_forall_le_add_small`, which between them supply: how close ANY
//! sufficiently fine SINGLE-interval Riemann sum sits to that interval's own
//! integral; a closeness bound at ONE boundary sample near `c` with fully
//! discharged domain-membership hypotheses; Archimedean smallness of a
//! scaled mesh step; and a way to conclude `Equiv` from an arbitrary-accuracy
//! bound — none of which, singly or combined, bound the cross-interval,
//! whole-sum discrepancy `integral_split` needs.
//!
//! `creal_prelude_builds`: unaffected by this entry (module documentation
//! only, no declaration added or changed).
//!
//! ## `CReal.integral_split` — checked 2026-08-27 (an EIGHTH lane), landed
//! [`CRealPrelude::crossing_sample_pairing_close`] (`crossing.rs`), the
//! term-PAIRING slice this task was sized down to, and hit a WALL one level
//! deeper than the seventh entry's — the wall is not (only) "no reblock
//! algebra applies", it is a **type-level mismatch inside `crossing.rs`
//! itself**.
//!
//! **What was buildable, and IS now kernel-checked**:
//! `crossingCloseClamped` specialized at `c := a + (ofNat i)·stepAb` (an
//! ordinary `[a,b]`-mesh sample point, `stepAb : CReal` arbitrary) gives,
//! for a **rational** `deltaAc`, `close_within (F ptI) (F clampedPt)
//! (1/(e+1))` where `clampedPt := min (a + (ofNat (crossingIndex a ptI
//! deltaAc))·(ofRat deltaAc)) b` — the index map `j(i) := crossingIndex a
//! ptI deltaAc`, COMPUTED (no `Exists.rec`), no `Nat.sub` anywhere. Verified
//! by hand at `i := 0` (`ptI` reduces to `a`, so `j(0) = crossingIndex a a
//! deltaAc`, and every hypothesis the theorem needs at that instance is
//! trivial `le_refl`-shaped) and symbolically at arbitrary `i` (the theorem
//! is universally quantified over `i`, so there is no separate "boundary"
//! case to special-case: `crossingIndex`'s own recipe is total in its
//! target argument, unlike a hand-rolled `floor`/`Nat.sub` map would be).
//! `creal_prelude_builds`: **23.88s** against a same-session baseline in the
//! 20-22.4s band (noise-dominated, one declaration) —
//! `every_creal_declaration_is_checked_and_axiom_free` (`--release`)
//! confirms it is a checked, axiom-free `Theorem`.
//!
//! **Why "rational `deltaAc`" is not a stylistic choice but the actual
//! boundary of what type-checks**: `crossingIndex`'s (hence
//! `crossingCloseClamped`'s) step parameter is `Rat`, not `CReal` —
//! `declare_crossing_index`'s `delta_fv` is bound at `rat_ty_` in the
//! kernel, and `build_scaled` computes `Rat.inv delta`, a DECIDABLE
//! rational inverse. The natural cross-mesh step for an ARBITRARY split
//! point `c`, `deltaAc := (c−a)·ofRat(natDivSucc 1 m_ac)`, is `CReal`-valued
//! whenever `c−a` is not itself rational — so `crossingIndex a ptI deltaAc`
//! **does not even parse** for a general `c`, let alone need a soundness
//! argument. This is the SAME "not a computable rational multiple" fact the
//! seventh entry names, sharpened from "no algebra applies" to the precise
//! signature that blocks it.
//!
//! **The rescue that does NOT work for free**: this prelude's only
//! `CReal`-level inverse, `CReal.inv (x) (k) (h : PosBound x k) : CReal`
//! (`creal/inverse.rs`, ADR-0510 phase F3), could build `(c−a)⁻¹` given an
//! explicit positivity witness — but `crossing.rs`'s internal recipe
//! (`build_scaled`, `scale_cancels`, the four `bucketIndex` closeness
//! lemmas' composition) is hard-wired to `Rat.inv` throughout; none of it is
//! stated against `CReal.inv`. Pre-rescaling `ptI` by `(c−a)⁻¹` so
//! `crossingIndex` only ever sees a literal `Rat` delta is possible in
//! principle, but the resulting closeness bound would be stated in the
//! RESCALED (unit) coordinate, and translating it back to a bound on `|ptI
//! − ptAc(j(i))|` in ORIGINAL units needs multiplying back through by the
//! `CReal` factor `(c−a)` — a REAL (not `Nat`, unlike
//! [`CRealPrelude::mesh_scaled_le_of_ge`]) scaling step with no existing
//! lemma covering it. That is a genuinely new sub-development, not a
//! wiring exercise, and is NOT attempted here.
//!
//! **What this slice does NOT reach**: the block-level summation
//! (`abs_sumRange_le` + `sumRange_le` over the paired terms) was not
//! attempted — it needs, in addition to the general (non-rational-`deltaAc`)
//! pairing lemma above, a Nat-arithmetic bound placing `j(i) ≤ m_ac` for
//! every `i` up to the crossing index (so `ptAc(j(i))` is an actual term of
//! `riemannSum F a c m_ac`, not merely a nearby real value), which is itself
//! unbuilt. **Negative control, checked**: this pairing lemma's conclusion
//! is an inequality (`close_within`, i.e. `abs (…) ≤ ofRat (1/(e+1))`)
//! gated entirely behind caller-supplied `h_upper`/`h_lower` hypotheses that
//! themselves encode mesh fineness — there is no substitution of `m_ac`
//! (equivalently, of `deltaAc`) that turns this into an unconditional claim,
//! so it cannot collapse into the false fixed-mesh interval-additivity
//! equality the task's negative control names.
//!
//! **Recommended next slice**: EITHER (a) restrict `integral_split`'s own
//! statement to the case `c := a + ofRat q` (`q : Rat`, giving `deltaAc :=
//! q·natDivSucc(1,m_ac)`, directly usable by
//! [`CRealPrelude::crossing_sample_pairing_close`] as built) and prove the
//! rational-split-point special case of interval additivity first, or (b)
//! build the real-scaled analogue of `mesh_scaled_le_of_ge` needed to
//! translate a `CReal.inv`-rescaled closeness bound back to original units,
//! which unblocks the general `c`.
//!
//! ## `CReal.integral_split` — checked 2026-08-27 (a NINTH lane), took fork
//! (b) — a MUCH easier route than the general case, and it is now landed as
//! `CReal.riemannSum_split_exact`
//!
//! Task: restrict the split point to `c := a + q·(b−a)`, `q : Rat`,
//! `0 < q < 1`, and check whether the resulting mesh-splitting bridge is pure
//! index algebra, per this file's own eighth entry's suggested next slice.
//!
//! **The hand computation confirms exact alignment, and it generalizes
//! further than expected.** At `a := 0, b := 3, q := 1/3, k := 2` (so
//! `n_ac := 2, n_cb := 4, n_ab := 6`, `c := 1`): `riemannSum(F,a,b,5) =
//! riemannSum(F,a,1,1) + riemannSum(F,1,3,3)` EXACTLY, checked for both
//! `F := const 2` (`6 = 2 + 4`) and `F := id` (`3.75 = 0.25 + 3.5`) by hand
//! summation. The false fixed-mesh counterexample the task named (`m := 0`
//! shared across all three intervals: `0 = riemannSum(id,0,3,0)` vs
//! `2 = riemannSum(id,0,1,0) + riemannSum(id,1,3,0)`) fails for a precise,
//! checkable reason: it uses `n_ac = n_cb = n_ab = 1`, and `1 ≠ 1+1` — it
//! violates the ONE identity (`n_ab = n_ac + n_cb`) alignment actually
//! needs, not some subtler estimate.
//!
//! **The general lemma needs no rationality of `q` at all.** Deriving the
//! mesh-count identity `n_ab = n_ac + n_cb ⟹ Δ_ac = Δ_cb = Δ_ab EXACTLY`
//! only uses that `c` IS a sample point of a refined `[a,b]` mesh —
//! `c := a + (ofNat (succ m_ac))·Δ_ab` — never that `c−a` is a rational
//! multiple of `b−a`. So the buildable core is STRICTLY more general than
//! the rational-split-point slice this task was sized for: it is a
//! `riemannSum` interval-split identity for ANY `c` the caller can express
//! as such a mesh point, symbolic `m_ac`/`m_cb` included. Landed as
//! [`CRealPrelude::riemann_sum_split_exact`]
//! (`declare_riemann_sum_split_exact`, this file) — **kernel-checked**,
//! `creal_prelude_builds` unaffected (22–25 s, within this session's
//! 20–24 s noise band), and confirmed at a concrete, discriminating
//! instantiation (`F := id`, not a constant — `riemannSum(const k,a,b,m) =
//! k·(b−a)` for EVERY `m`, so a constant `F` cannot tell an aligned split
//! from a misaligned one; `a:=0, b:=3, m_ac:=1, m_cb:=3`, matching the hand
//! computation's `q := 1/3, k := 2` case) against an INDEPENDENTLY rebuilt
//! expected statement, not merely inferred.
//!
//! Proof shape: `H_split` (`width_of(a,b) ~ w1+w2`, `w_i := ofNat(n_i)·Δ_ab`,
//! via [`CRealPrelude::of_nat_add`] + [`right_distrib`] +
//! [`CRealPrelude::mesh_count_width`] — no `CReal.inv`, no crossing index);
//! `H_b`/`H_cb` (uncancel/cancel that width equation to place `c` between
//! `a` and `b`, and derive `width_of(c,b) ~ w2`); two
//! `delta_from_width_equiv` calls (`Δ_ac ~ Δ_ab`, `Δ_cb ~ Δ_ab` — EQUAL, not
//! merely close); then [`CRealPrelude::sum_range_split`] (`succ m_ab`
//! defeq `add (succ m_ac)(succ m_cb)` by pure `Nat.add` right-recursion, no
//! `succ_add` rewrite needed — the SAME `succ_mul_succ` trick this file
//! already uses for `*`, reused for `+`) plus two
//! [`CRealPrelude::sum_range_congr`] calls to glue the split sum back into
//! the two child `riemannSum`s.
//!
//! **The one genuinely new hypothesis, and it is NOT avoidable**: `F`
//! respecting `Equiv` (`∀ x y, Equiv x y → Equiv (F x) (F y)`), threaded as
//! an explicit parameter (`hcong`). `Δ_ac ~ Δ_ab` is `Equiv`, not `Eq`, so the
//! two mesh points `a+i·Δ_ab` and `a+i·Δ_ac` an arbitrary `F : CReal → CReal`
//! is applied to are only `Equiv`, never definitionally equal, once the mesh
//! is refined — and nothing about a raw `CReal → CReal` function forces it to
//! respect that relation. This is a MUCH weaker requirement than a full
//! `UniformlyContinuousOn` modulus (no rate, just the bare implication), but
//! it is not zero.
//!
//! **What this slice does NOT reach, precisely two gaps, both assembly, not
//! new estimates:**
//! 1. Connecting an arbitrary rational `q` (`c := a + ofRat(q)·(b−a)`) to a
//!    SPECIFIC `(m_ac, m_cb)` pair this lemma accepts — writing
//!    `q = p/(succ r)` and choosing `m_ac := p·k − 1`-shaped counts (for a
//!    multiplier `k`) so `c` literally lands on `a + (ofNat(succ m_ac))·Δ_ab`.
//!    Pure `Rat`/`Nat` bookkeeping (no estimate), NOT attempted here; the
//!    landed lemma is strictly more general than needing it, so this is
//!    optional polish for a rational-`q`-shaped public statement, not a
//!    blocker for reuse.
//! 2. Deriving `hcong` from an actual continuity witness (e.g.
//!    `UniformlyContinuousOn F a b`) — `uniformly_continuous_imp_continuous_at`
//!    (`uniform_continuity.rs`'s own module documentation) is the named,
//!    not-yet-landed bridge this needs, and then relating `riemannSum` to
//!    `CReal.integral` via [`CRealPrelude::riemann_sum_integral_close`] on
//!    all three intervals plus `le_of_forall_le_add_small`/
//!    `equiv_zero_of_small` (per the 2026-08-27-earlier entry) to close the
//!    outer `Equiv` on `CReal.integral` values themselves. NOT attempted
//!    here — this is where the real estimate-shaped work still lives.
//!
//! **Negative control, tried and removed rather than debugged**: a
//! kernel-level test asserting the SAME concrete proof term against a
//! statement with `m_ac`/`m_cb` swapped between the two `riemannSum` calls
//! drove the typechecker into unbounded work (>2:35 wall-clock at 99.9% CPU,
//! RSS still climbing past 2.6 GB when killed — not a stack overflow). Per
//! this file's own "a symbolic test can be pathological" convention: deleted
//! rather than chased, and recorded here rather than silently dropped.
//!
//! ## `CReal.integral_split` — checked 2026-08-27 (a TENTH lane), gap 2's
//! two remaining pieces landed; the final estimate assembly NOT attempted
//!
//! Gap 2 above named two pieces: deriving `hcong` from a
//! `UniformlyContinuousOn` witness, and relating `riemannSum` to
//! `CReal.integral` on all three intervals. **Both prerequisites this lane
//! was briefed against already existed by the time it started**:
//! [`CRealPrelude::riemann_sum_split_exact_of_uc`] (discharges the split
//! identity from a `UniformlyContinuousOn` witness directly, no `hcong`
//! needed at all — a later lane's stronger route than gap 2's own plan) and
//! [`CRealPrelude::riemann_sum_integral_close`] (riemannSum-vs-`integral`,
//! already landed). The one piece that did NOT exist is the sub-interval
//! restriction `UniformlyContinuousOn` needs to turn ONE witness on `[a,b]`
//! into witnesses on `[a,c]`/`[c,b]` for the two child integrals —
//! `CReal.uniformlyContinuousOn_restrict` (`uniform_continuity.rs`, this
//! lane), built directly against `UniformlyContinuousOn.mk` with the SAME
//! modulus and kernel-checked (`creal_prelude_builds` unaffected, 32.5s
//! against a 32–38s baseline band).
//!
//! **The remaining estimate work, characterized precisely rather than
//! attempted, because it is the load-bearing piece and a wrong shortcut here
//! would be a soundness risk, not a missing convenience:**
//! [`CRealPrelude::riemann_sum_integral_close`]'s own bound
//! (`bound_leg1(e,depth,i,jj1,jj2) + natDivSucc(K,e)`, reconstructed from
//! [`CRealPrelude::riemann_sum_shared_accuracy_close`]'s conclusion) is
//! `modulus(l, shift(jj1)) + bound1(jj1) + modulus(shift(jj1), i)` plus a
//! symmetric second leg, where **`l := common_refinement(m1, m2).0`
//! (`m1 := deep(e)+depth`, `m2 := deep(e)+0`) is NOT the caller's choice of
//! `jj1`/`i` — it is baked into `riemann_sum_shared_accuracy_close`'s own
//! statement as the shared mid-anchor's sample point.** This differs from
//! [`declare_riemann_sum_deep_cauchy`]'s own use of the more primitive
//! [`CRealPrelude::shared_index_to_canonical`] (three FREE indices `pp, qq,
//! jj`, so it can choose `pp := pn` directly and avoid `l` in the bound
//! altogether) — `riemann_sum_shared_accuracy_close` is a less general,
//! already-composed theorem that cannot be re-parameterized this way without
//! rebuilding it.
//!
//! **The lever `l` responds to, and the reason this is still closable
//! without new mathematics**: `l` is a genuine `Nat` term (not an opaque
//! constant) that GROWS with `depth` regardless of what `u`'s own modulus
//! does, since `m1 := deep(e) + depth → ∞` as `depth → ∞` and
//! `l = succ_mul_succ(m2, m1).0` grows with `m1`. So `natDivSucc(1, l) → 0`
//! as `depth → ∞`, at every fixed `e` — the missing shrink is available, it
//! is just reached through `depth`, not through `e` or `jj1` the way the
//! other two `modulus` legs shrink.
//!
//! **`riemannSumTotalEpsLe`'s own consumer, [`total_eps_sample_le`], is
//! accuracy-locked to its sample index and must be generalized before this
//! assembly can use it.** `bound1(jj1) := sample(totalEps(a,b,e,m1),jj1) +
//! natDivSucc(2,jj1)` samples `totalEps` at `jj1`, a DIFFERENT index from the
//! accuracy `e` baked into `totalEps`'s own construction; `total_eps_sample_le`
//! as written applies `riemann_sum_total_eps_le`'s witness at the SAME index
//! used to build it (`d.apply(t, &[idx])`, one `idx` doing both jobs). The
//! generalization is mechanical, not new mathematics: `CReal.le`'s own
//! witness term can be `d.apply`'d at ANY raw index, so a two-index variant
//! (`total_eps_sample_le_at(a, b, e, m, magnitude, n)`, applying at `n`
//! instead of `e`) gives `sample(totalEps(a,b,e,m),n) ≤
//! natDivSucc(magnitude,e) + natDivSucc(2,n)` — a term depending on `e` and
//! `n` SEPARATELY, exactly what combining three intervals at independently
//! chosen accuracies needs. NOT built here: it has no consumer yet in this
//! file, and an unused private helper is a `-D warnings` clippy failure, so
//! landing it alone would be dead weight rather than progress.
//!
//! **The resulting recipe, worked out but not built**: pick ONE inner
//! accuracy `e_inner` and ONE large index `depth := jj1 := jj2 := i := N`
//! (all equal, all free choices `riemann_sum_integral_close` allows) on each
//! of the three interval applications ([a,b], [a,c], [c,b], the latter two
//! using [`CRealPrelude::uniformly_continuous_on_restrict`]'s witnesses).
//! Every term in the resulting bound is then one of: `natDivSucc(1, l(N,
//! e_inner))` (→0 as `N`→∞, via the lever above), `natDivSucc(c, N)` for
//! small literal `c` (→0 as `N`→∞, ordinary), `natDivSucc(magnitude_X,
//! e_inner)` for the three intervals' own `magnitude_X := succ(CReal.bound
//! (width_X))` (→0 as `e_inner`→∞, via `total_eps_sample_le_at` above), and
//! `natDivSucc(K_X, e_inner)` (the three `riemann_sum_integral_close`
//! witnesses' own rates, already closed-form). The middle `riemannSum`
//! equality is EXACT ([`CRealPrelude::riemann_sum_split_exact_of_uc`]), so
//! summing all three intervals' bounds and choosing `N`, `e_inner` as
//! explicit linear functions of the OUTER accuracy `equiv_zero_of_small`
//! names (enough slack to beat the finitely many fixed rational
//! coefficients) closes `integral_split`. This is genuinely assembly — every
//! lemma named above already exists or is a small mechanical generalization
//! of one that does — but it is roughly the same volume of exact `Rat`
//! bookkeeping as [`bnd_leg_plus_share_le`] (~150 lines) done THREE times and
//! then combined, plus the final `Nat`-valued choice of `N`/`e_inner`, and
//! was not attempted in this slice.
//!
//! ## `CReal.integral_split` — checked 2026-08-27 (a TWELFTH lane), the
//! mesh-count alignment gap the TENTH lane's plan glossed over is now
//! resolved on paper; the ~450-line assembly itself was NOT attempted in
//! code this slice, and `integral_split` remains UNDECLARED
//!
//! Starting point confirmed present and unchanged since the refactor lane:
//! [`CRealPrelude::riemann_sum_shared_accuracy_close_at`],
//! `total_eps_sample_le_at` (private, this file, generalizes
//! `total_eps_sample_le` off the shared-index assumption),
//! [`CRealPrelude::riemann_sum_split_exact_of_uc`],
//! [`CRealPrelude::riemann_sum_split_scale_invariant`],
//! [`CRealPrelude::close_within_of_within_indexed`],
//! [`CRealPrelude::uniformly_continuous_on_restrict`], and
//! [`CRealPrelude::integral_witness_independent`] all build, and their doc
//! comments confirm the shapes the TENTH lane's plan names.
//!
//! **A gap the TENTH lane's plan did not name, found by trying to actually
//! instantiate it: the THREE mesh counts `riemann_sum_integral_close`
//! produces on `[a,b]`, `[a,c]`, `[c,b]` are independently-shaped `Nat`
//! expressions (`deep_ab(e)+depth_ab`, `deep_ac(e)+depth_ac`,
//! `deep_cb(e)+depth_cb`, each `deep_X` a DIFFERENT modulus-of-uniform-continuity
//! function), and `riemannSum_split_exact_of_uc`'s identity needs the SPECIFIC
//! relation `combined = succ(m_ac) + m_cb`.** Picking `m_ac`/`m_cb` freely
//! (as the TENTH lane's plan does) leaves `combined` some `Nat` expression
//! with no reason to equal `deep_ab(e)+depth_ab` for ANY `depth_ab` — the
//! obvious fix (`depth_ab := combined - deep_ab(e)`) is exactly the
//! `Nat.sub`-truncation trap this file's own kernel-facts list warns about,
//! since nothing bounds `deep_ab(e) ≤ combined` a priori.
//!
//! **Resolved by NOT computing `depth_ab` at all — derive its EXISTENCE
//! instead, [`declare_of_nat_le`]'s own idiom (`Nat.le_dest` +
//! `exists_elim`), never Nat.sub:**
//!
//! 1. Fix `e`, and choose `depth_ac := depth_cb := add(deep_ab(F,a,b,u,e),
//!    bigN)` for a genuinely free `bigN` (the parameter actually driven to
//!    infinity against `e` below) — i.e. bake `deep_ab(e)` itself into both
//!    child depths, so it is *available* as a term inside `combined` without
//!    needing to match it structurally.
//! 2. `m_ac := add(deep_ac(F,a,c,uac,e), depth_ac)`,
//!    `m_cb := add(deep_cb(F,c,b,ucb,e), depth_cb)`,
//!    `combined := add(succ(m_ac), m_cb)` — built literally this way, so it
//!    is [`CRealPrelude::riemann_sum_split_exact_of_uc`]'s own `m_ac`/`m_cb`
//!    argument shape verbatim.
//! 3. Prove `Nat.le (deep_ab(F,a,b,u,e)) combined` by a **four-hop
//!    `le_trans` chain over EXISTING lemmas only** — `le_add_right`
//!    (`deep_ab(e) ≤ add(deep_ab(e),bigN)`), then `le_add_right` again composed
//!    through an `add_comm` via `nat_rewrite_prop` (to place the depth term on
//!    the correct side of `m_ac`'s sum), `le_succ`, `le_add_right` once more
//!    for the final `+m_cb`. No `add_assoc`/`add_right_comm` reassociation of
//!    more than two terms at a time is needed anywhere in this chain — every
//!    step is a single named lemma or one `nat_rewrite_prop` transport across
//!    `Nat.add_comm`.
//! 4. `Nat.le_dest` on that `le` fact gives `∃ depth_ab, add(deep_ab(e),
//!    depth_ab) = combined`; `exists_elim` (already imported in this file)
//!    binds `depth_ab` and the equation for the rest of the proof, exactly
//!    the shape [`declare_of_nat_le`] already uses to avoid needing
//!    definitional equality of two independently-built `Nat` sums.
//!    `riemann_sum_integral_close`'s `[a,b]` application at this `depth_ab`
//!    then transports across that equation via `nat_rewrite_prop`, landing
//!    on a `Within` fact about `riemannSum F a b combined` on the nose —
//!    the exact LHS [`CRealPrelude::riemann_sum_split_exact_of_uc`] needs.
//!
//! `hac`/`hcb`/`c` for this specific `(m_ac, m_cb)` are NOT re-derived from
//! scratch: [`declare_riemann_sum_split_exact_of_uc`]'s own body computes
//! them from `w1`/`w2`'s nonnegativity via `shift_le_of_nonneg`/
//! `zero_le_of_nat`/`cancel_width` (all already free functions in this
//! file), and the same three calls at this lane's own `(m_ac, m_cb)` values
//! give the witnesses [`CRealPrelude::uniformly_continuous_on_restrict`]
//! needs for `uac`/`ucb`.
//!
//! **What this leaves, sized as precisely as the mesh-alignment piece just
//! was, and NOT attempted in code this slice**: the final combine is
//! `abs_add_le` (the triangle inequality) applied twice against
//! `riemannSum_split_exact_of_uc`'s exact identity substituted in via
//! `le_congr`, closed by `equiv_zero_of_small` once all three
//! `riemann_sum_integral_close` bounds (each `bound_leg1(e,depth,i,jj1,jj2) +
//! natDivSucc(K,e)`, `bound_leg1` itself a `modulus`/`shared_accuracy_bound`
//! compound needing the SAME `bnd_leg_plus_share_le`-style weakening this
//! file already does once per leg) are shown `≤` a fixed fraction of
//! `natDivSucc(1, e)` for `bigN`/`e_inner` chosen as explicit functions of
//! `e`. That estimate volume is UNCHANGED from the TENTH lane's own sizing —
//! roughly `bnd_leg_plus_share_le` (~150 lines) three times plus the
//! three-way triangle combine — and stacks on top of, not instead of, the
//! mesh-alignment piece resolved above. Concrete corroboration
//! (`F := const two`/`F := id`, split at `a:=0,b:=3,c:=1`) was NOT run: there
//! is no declaration to corroborate. `integral_split` is not registered in
//! `CRealPrelude`, has no `BuildStep`/`EXPECTED_STEP_ORDER` entry, and no
//! inventory shard row; `creal_prelude_builds` is unaffected by this slice
//! (doc-only change).
//!
//! ## `CReal.integral_split` mesh-count alignment — LANDED 2026-08-27 (a
//! THIRTEENTH lane), the TWELFTH lane's paper resolution above is now a
//! kernel-verified private helper, [`mesh_count_align`]
//!
//! The Nat.le chain + `Nat.le_dest` + `exists_elim` resolution the TWELFTH
//! lane worked out on paper (steps 1–4 above) worked EXACTLY as designed, no
//! adjustment needed: the four-hop `le_trans` chain
//! (`le_add_right`/`le_add_right`+`add_comm` via [`nat_rewrite_prop`]/
//! `le_succ`/`le_add_right`) composes cleanly, and `Nat.le_dest` +
//! [`exists_elim`] (continuation-passing, since the witness cannot escape
//! its own elimination scope, [`declare_of_nat_le`]'s own idiom) closes it.
//! Kernel-verified three ways: symbolic (closed over four free `Nat`
//! variables via a real `Theorem` declaration), a non-vacuity control
//! (swapping `deep_ac`/`deep_cb` changes the rendered `combined`, since
//! `succ` binds only the `deep_ac` side), and a concrete instantiation
//! (`3,5,7,2 → combined` defeq `23`, checked via `Kernel::def_eq` — a
//! textual `render_lean` comparison does NOT reduce `Nat.add`, and reported
//! a false mismatch before this was noticed).
//!
//! [`common_refinement3`] was checked against this need and does NOT fit:
//! it refines two mesh counts against a shared TARGET refinement multiple,
//! not three counts against a SUM relation — a structurally different
//! problem, so nothing here duplicates it.
//!
//! `mesh_count_align` is a private helper with its own `#[cfg(test)]`
//! module, wired into no `CRealPrelude` field, no `BuildStep`, no
//! `EXPECTED_STEP_ORDER` entry, and no inventory shard row —
//! `creal_prelude_builds` is unaffected.
//!
//! ## `CReal.integral_split` `[a,c]`-leg bound-weakening — LANDED 2026-08-27
//! (a FOURTEENTH lane), `bnd_leg_plus_share_le_at`
//!
//! [`bnd_leg_plus_share_le_at`] is [`bnd_leg_plus_share_le`]'s independent-
//! accuracy/sample-index generalization: same `a1`/`a2`/`shift`/`b1`
//! bookkeeping, same `half_shift_le`-weakened `modulus` pair, same fold into
//! a single `natDivSucc`, but the `bound_at_idx` weakening step consumes
//! [`total_eps_sample_le_at`] at an accuracy `e` and a sample index `jj1`
//! that are never assumed equal (`e := jj1` recovers `bnd_leg_plus_share_le`
//! exactly, since `total_eps_sample_le` is that specialization).
//!
//! **The one genuine obstacle, not visible until the fold was attempted**:
//! `m_term := natDivSucc(magnitude, e)` and every other leaf (`a1`/`a2`/`b1`)
//! are built at `jj1`, and [`fuse_nds`] only fuses two `natDivSucc`s at the
//! SAME index. So `m_term` cannot join the fold at all — it is pulled to the
//! front of the sum instead: one `Rat.add_assoc` isolates `b1+b1`, one
//! [`reassoc3`] application moves `m_term` past the first `a1a1`, and from
//! there every remaining step is a plain `Rat.add_assoc` (never another
//! commute) because `m_term` is already in front. The final shape is
//! `Rat.le (bnd_leg_actual + natDivSucc(1,jj1)) (m_term + natDivSucc(k,jj1))`
//! — `k` defeq `9` at concrete inputs, matching `bnd_leg_plus_share_le`'s own
//! `magnitude + 9` leaf count with `magnitude`'s term now carried separately.
//!
//! **`magnitude` is not an independent input, and treating it as one is the
//! mistake that cost this lane its first two failed attempts.**
//! `riemann_sum_total_eps_le`'s own conclusion embeds `succ(CReal.bound
//! (width_of a b))` as ITS magnitude; a caller's `magnitude` argument must be
//! that SAME `ExprId` (`width_of` then [`direct_bound_le`], hash-consed) or
//! `total_eps_sample_le_at`'s own internal `le_of_sub_le` application fails
//! to type-check — invisible in `d.lemma`'s construction, surfacing only when
//! the whole closed term is inferred, and failing identically whether `a`/`b`
//! are symbolic or concrete (an arbitrary literal magnitude at CONCRETE `a
//! := zero, b := one` is just as wrong; nothing about concreteness excuses
//! deriving `magnitude` correctly). `total_eps_sample_le_at`'s own test
//! already used this exact recipe — the miss was not rereading it before
//! picking a convenient value.
//!
//! Kernel-verified three ways, mirroring `mesh_count_align_tests`: symbolic
//! (closed over `a b e jj1 m` via a real `Theorem`, `magnitude` derived from
//! `a`/`b` rather than separately quantified), a non-vacuity control
//! (swapping `e`/`jj1` changes the rendered target, since `e` appears only in
//! `m_term` and `jj1` only in the folded side), and a concrete instantiation
//! (`e:=6, jj1:=3, m:=6, a:=zero, b:=one` — `k` defeq `9` via `Kernel::def_eq`).
//! `bnd_leg_plus_share_le_at` is a private helper with its own `#[cfg(test)]`
//! module, wired into no `CRealPrelude` field, no `BuildStep`, no
//! `EXPECTED_STEP_ORDER` entry, and no inventory shard row —
//! `creal_prelude_builds` is unaffected (33 s, unchanged from baseline).
//!
//! **The `[c,b]` leg needs NO new derivation — it is the SAME function,
//! called at different arguments.** The `succ` in `mesh_count_align`'s
//! `combined := add(succ(m_ac), m_cb)` is bookkeeping for how the two legs'
//! mesh counts combine into `riemann_sum_split_exact_of_uc`'s identity; it
//! never appears inside a leg's OWN Cauchy-bound-weakening, which only ever
//! sees ITS OWN mesh count as an opaque `jj1`. So the `[c,b]` leg is
//! `bnd_leg_plus_share_le_at(d, p, c, b, e, m_cb, m, magnitude_cb,
//! bound_at_idx_cb)` — the identical call with `(c,b,m_cb,magnitude_cb)` in
//! place of `(a,c,m_ac,magnitude_ac)` — not a mirror-image derivation to
//! write. What remains is the final three-way `abs_add_le` combine sized in
//! the TWELFTH lane's own entry above (unchanged by this landing).
//!
//! ## `CReal.integral_split` — checked 2026-08-27 (a FIFTEENTH lane), the
//! assembly was NOT attempted in code; TWO gaps found that no prior entry
//! names, one of which makes [`mesh_count_align`] unusable for a general
//! split ratio as landed
//!
//! Starting point confirmed unchanged: [`mesh_count_align`] and
//! [`bnd_leg_plus_share_le_at`] both build and both pass their own tests
//! post-merge; `creal_prelude_builds` is 31.5 s (band 29-39 s). Before
//! writing the ~450-line combine, this lane worked out EXACTLY which
//! `ExprId`s the combine's three legs must share (`riemann_sum_integral_close`
//! on `[a,b]`, `[a,c]`, `[c,b]`; `close_within_of_within_indexed` bridging
//! each `Within` to a `CReal.le (abs …)`; [`declare_riemann_sum_split_exact_of_uc`]'s
//! exact identity substituted in via `le_congr`), and found two obstacles
//! neither the TENTH, TWELFTH, THIRTEENTH nor FOURTEENTH lane's sizing
//! mentions.
//!
//! **Gap A: [`mesh_count_align`]'s padding scheme forces the split ratio
//! toward the MIDPOINT as its own `big_n` grows, for any target ratio other
//! than 1:1 — confirmed by direct computation, not just inspection.**
//! `mesh_count_align` fixes `depth_ac := depth_cb := add(deep_ab, big_n)`
//! (the SAME padding term for both legs, per its own doc comment above).
//! `riemann_sum_split_exact_of_uc`'s split point is exactly `a +
//! ofNat(succ m_ac) * delta_of(a,b,combined)`, i.e. the ratio `succ(m_ac) :
//! combined`. At `m_ac0 := 0, m_cb0 := 3` (an intended 1:4 split, `c` at
//! 20% of `[a,b]`), `deep_ab := 2, deep_ac := 1, deep_cb := 1`, this ratio
//! measures:
//!
//! ```text
//! big_n =     10 -> ratio 0.5185
//! big_n =    100 -> ratio 0.5024
//! big_n =  10000 -> ratio 0.50002
//! big_n = 1e6    -> ratio 0.500000
//! ```
//!
//! — converging to **0.5**, not the intended **0.2**, because `big_n` is
//! ADDED identically to both legs' mesh counts and therefore dominates and
//! equalizes them as it grows, regardless of `m_ac0`/`m_cb0`. Since
//! `equiv_zero_of_small` needs the mesh counts to grow WITHOUT BOUND as the
//! outer accuracy `e` does (so `big_n` cannot be held at a small fixed
//! value), [`mesh_count_align`] as landed can only support the bisection
//! case (`m_ac0 = m_cb0`) — for which the drift target (midpoint) happens
//! to coincide with the intended one — and NOT the general "every rational
//! proportion" claim [`declare_riemann_sum_split_exact_of_uc`]'s own
//! ADR-0603 stratum aims for. `riemann_sum_split_scale_invariant` cannot
//! rescue this after the fact either: it only proves the split point fixed
//! for the *multiplicative* `succ_mul_succ` family (`m_ac_k`/`m_cb_k` both
//! scaled by the SAME factor `succ k`), which [`mesh_count_align`]'s
//! additive `deep_ac + (deep_ab+big_n)` shape does not belong to for any
//! `big_n`. The fix is a differently-parameterized alignment helper (or a
//! generalized [`mesh_count_align`]) that pads `m_ac`/`m_cb` by
//! `n_ac0 * (deep_ab+big_n)` / `n_cb0 * (deep_ab+big_n)` respectively (or
//! goes through `succ_mul_succ` directly, proving `deep_X(e) ≤ m_X_k` for
//! the multiplicative family by a separate Archimedean argument) — not
//! attempted here; this is new scope, not a rewiring of what exists.
//!
//! **Gap B: nothing in this file (or elsewhere in `creal/`) lets a `CReal
//! .integral` taken at one endpoint be related to the SAME integral at an
//! `Equiv` — not equal — endpoint, and the combine needs exactly that.**
//! Even with Gap A fixed, `riemann_sum_split_exact_of_uc(F,a,b,m_ac,m_cb,
//! u,hab)`'s split point `c` is whatever `a + ofNat(succ m_ac) *
//! delta_of(a,b,combined)` computes to for the mesh counts actually used at
//! a given outer accuracy `e` — call it `c_e`. `integral_split`'s STATED
//! conclusion needs a single FIXED `c` (with fixed `hac`/`u_ac`/`hcb`/
//! `u_cb`, supplied once by the caller), so closing it needs `integral F a
//! c_e hac_e u_ac_e` related to `integral F a c hac u_ac` for `c_e` merely
//! `Equiv c` (never definitionally equal, since `c_e` is a fresh Nat
//! arithmetic expression at every `e`). [`CRealPrelude::integral_witness_independent`]
//! is the closest existing lemma and does NOT cover this: its own two
//! endpoints are the SAME `b`, varying only the *witness* (`u1` vs `u2`);
//! nothing here varies the endpoint itself. Note too that this cannot be
//! discharged by a `riemannSum`-level congruence in `b` under `Equiv`, even
//! in principle: `riemannSum`'s value at a sample index is a RATIONAL
//! (`sample x n`), and two `Equiv` `CReal`s are only guaranteed to agree in
//! the LIMIT, never sample-by-sample — so any bridge has to go through the
//! `CReal`-level `Equiv`/`le_congr` route (the same one
//! [`declare_integral_witness_independent`] already uses for its own,
//! narrower, same-endpoint case), which is why this is a genuinely new
//! lemma (`integral_congr_endpoint`, sketched but not built: same
//! `Converges`/`riemann_sum_deep_cauchy_cross`-family route as
//! `integral_witness_independent`, with the cross-bridge additionally
//! needing to relate `f_lambda`'s own mesh-count family across the two
//! `b`s) rather than a rewiring of anything landed.
//!
//! **Net effect on sizing**: the combine's own volume (three-way
//! `abs_add_le`, one `bnd_leg_plus_share_le_at` call per leg,
//! `le_of_forall_le_add_small`/`equiv_zero_of_small` to close) is unchanged
//! from the TWELFTH lane's own estimate, but it now has two PREREQUISITES
//! neither the TENTH, TWELFTH, THIRTEENTH nor FOURTEENTH lane's sizing
//! counted: a re-parameterized mesh-alignment helper (Gap A, comparable in
//! size to [`mesh_count_align`] itself, ~100 lines) and a new
//! `integral_congr_endpoint` lemma (Gap B, comparable in size to
//! [`declare_integral_witness_independent`], ~70-100 lines). Neither was
//! attempted in code this slice: writing either without kernel-verifying it
//! risks exactly the "checker that cannot fail" and "certificate must carry
//! every distinction" failure modes this repository's own CLAUDE.md warns
//! against, and this lane's remaining budget did not cover both plus the
//! combine itself with the compile-and-verify cadence the file's own
//! kernel-facts list requires. `integral_split` is not registered in
//! `CRealPrelude`, has no `BuildStep`/`EXPECTED_STEP_ORDER` entry, and no
//! inventory shard row; `creal_prelude_builds` is unaffected (doc-only
//! change, confirmed 31.5 s post-merge, same band as the FOURTEENTH lane's
//! 33 s).
//!
//! ## `CReal.integral_split` — 2026-08-27 (a SIXTEENTH lane), Gap A resolved
//! in the direction the FIFTEENTH lane conjectured: a MULTIPLICATIVE
//! alignment preserves an arbitrary rational ratio EXACTLY, at every scale
//!
//! **First, a correction to the FIFTEENTH lane's own numbers, which does not
//! change its conclusion but does change how bad the situation is.** That
//! entry computed the split ratio as `succ(m_ac) / combined`. The correct
//! fraction is `succ(m_ac) / (combined + 1)`: `riemann_sum_split_exact`'s
//! `c := a + ofNat(succ m_ac) * delta_of(a, b, combined)` and `delta_of a b m
//! := (b − a) * natDivSucc(1, m)` = `(b − a)/(m + 1)`, so
//!
//! ```text
//! (c − a)/(b − a) = succ(m_ac) / (combined + 1)
//!                 = n_ac / (n_ac + n_cb),   n_X := m_X + 1
//! ```
//!
//! since `combined + 1 = succ(m_ac) + succ(m_cb)`. Read correctly, the
//! additive scheme is worse than "drifting": with `mesh_count_align`'s own
//! `depth_ac := depth_cb := deep_ab + big_n` and `deep_ac = deep_cb`, the
//! ratio is **exactly 0.5 for every `big_n`, including `big_n = 0`** — not
//! 0.5185 → 0.5024 → 0.50002 converging to it. Recomputed:
//!
//! ```text
//! deep_ab=2, deep_ac=deep_cb=1:    big_n = 0, 10, 100, 1e4, 1e6 -> 0.5 exactly, every time
//! deep_ab=2, deep_ac=1, deep_cb=7: 0.2857 -> 0.4118 -> 0.4860 -> 0.49985 -> 0.4999985
//! ```
//!
//! The asymmetric row is the only one that moves, and it moves TOWARD 0.5.
//! And note what the symmetric row means: [`mesh_count_align`] has **no ratio
//! input at all** — its parameters are `deep_ab`, `deep_ac`, `deep_cb`,
//! `big_n`, three of which are uniform-continuity moduli the caller does not
//! choose. There is nowhere to put `(m_ac0, m_cb0)`. So the FIFTEENTH lane's
//! verdict stands and is strengthened: **as landed, [`mesh_count_align`]
//! supports the MIDPOINT only**, and the "every rational proportion" stratum
//! that [`declare_riemann_sum_split_exact_of_uc`]'s ADR-0603 entry aims at is
//! not reachable through it by any choice of its arguments.
//!
//! **Second, the multiplicative hypothesis: CONFIRMED, and exactly, not
//! asymptotically.** Take the base ratio `(m_ac0, m_cb0)` and scale both
//! counts through [`succ_mul_succ`] at a common factor `succ k`:
//! `m_ac_k := succ_mul_succ(m_ac0, k).0`, `m_cb_k := succ_mul_succ(m_cb0, k).0`,
//! so `succ(m_ac_k) = succ(m_ac0)·succ(k)` and likewise for `cb`. Then
//!
//! ```text
//! ratio = succ(m_ac0)·succ(k) / ((succ(m_ac0) + succ(m_cb0))·succ(k))
//!       = succ(m_ac0) / (succ(m_ac0) + succ(m_cb0))
//! ```
//!
//! — the `succ(k)` cancels identically, so the ratio is the base ratio for
//! EVERY `k`, with no limit taken. Checked as exact `Fraction` arithmetic at
//! `(m_ac0, m_cb0) ∈ {(0,3), (0,0), (2,5), (4,1), (9,90)}` and
//! `k ∈ {0, 1, 2, 3, 10, 100, 1e4, 1e6}`: 40 of 40 exactly equal to the base
//! ratio (1/5, 1/2, 1/3, 5/7, 10/101 respectively). This is the same family
//! [`CRealPrelude::riemann_sum_split_scale_invariant`] already proves
//! `Equiv c_k c_0` for — that theorem is the kernel-verified statement of
//! precisely this cancellation, and it is why the multiplicative route was
//! worth testing before building anything.
//!
//! **Third, the piece that made the additive scheme necessary in the first
//! place — clearing the three accuracy thresholds — survives the switch, and
//! gets SHORTER.** [`mesh_count_align`] bakes `deep_ac`/`deep_cb` into the
//! mesh counts syntactically (`m_ac := deep_ac + depth_ac`) precisely so
//! `deep_ac ≤ m_ac` needs no proof; that is exactly what forces the additive
//! shape. The multiplicative family cannot do that, so all three thresholds
//! become obligations — but all three follow from ONE inequality:
//!
//! ```text
//! succ_mul_succ(m0, k).0 = (m0·k + m0) + k  >=  k        [Nat.le_add_left]
//! ```
//!
//! so picking `k := ((deep_ab + deep_ac) + deep_cb) + big_n` gives
//! `deep_ac ≤ k ≤ m_ac_k`, `deep_cb ≤ k ≤ m_cb_k`, and
//! `deep_ab ≤ k ≤ m_cb_k ≤ combined`, each by a `le_trans` over
//! `le_add_left`/`le_add_right` only. Randomised check over 200,000 draws of
//! `(deep_ab, deep_ac, deep_cb, m_ac0, m_cb0, big_n)`: **0 counterexamples**.
//! Negative control (`k := big_n` alone, dropping the moduli from the scale
//! factor): **1,435 counterexamples in 20,000 draws**, so the check is not
//! vacuous. `big_n` remains free and drives all three counts to infinity, as
//! `equiv_zero_of_small` requires.
//!
//! **Fourth, Gap A is LANDED as [`mesh_count_align_mul`]** — the
//! multiplicative alignment above, kernel-verified four ways: the `[a,b]`
//! combined threshold symbolic in all six inputs; BOTH child thresholds
//! (`deep_ac ≤ m_ac`, `deep_cb ≤ m_cb`), which [`mesh_count_align`] never had
//! to prove because it obtained them by *defining* `m_ac := deep_ac +
//! depth_ac`; ratio preservation cross-multiplied into `Nat` and checked by
//! `Kernel::def_eq` at four base ratios × four scales; and a negative control
//! asserting the ADDITIVE counts FAIL that same identity at a 1:5 base ratio,
//! so the positive test is discriminating rather than an arithmetic tautology.
//! Two small private helpers came out of it: [`nat_le_add_left`] (the prelude
//! has `le_add_right` only) and [`le_dest_elim`] ([`mesh_count_align`]'s own
//! `Nat.le_dest` + [`exists_elim`] tail, factored so three can nest).
//!
//! ## `CReal.integral_split` — Gap B (SIXTEENTH lane, same day): load-bearing,
//! but it is a `riemannSum` congruence and NOT the `integral` congruence the
//! FIFTEENTH lane sized — and the "impossible even in principle" argument
//! against it is refuted by a kernel-checked term
//!
//! **Gap B is NOT avoidable by construction, and the "shared literal `c`"
//! hypothesis fails for a reason worth writing down.** The combine's mismatch
//! is visible only once the three legs are named:
//!
//! ```text
//! (A) riemann_sum_integral_close on [a, b] at `combined`        -> riemannSum F a b combined
//! (B) riemann_sum_integral_close on [a, c] at `m_ac`            -> riemannSum F a c   m_ac
//! (C) riemann_sum_integral_close on [c, b] at `m_cb`            -> riemannSum F c b   m_cb
//! (D) riemann_sum_split_exact_of_uc(F, a, b, m_ac, m_cb, u, hab)
//!       -> Equiv (riemannSum F a b combined)
//!                (add (riemannSum F a c_k m_ac) (riemannSum F c_k b m_cb))
//! ```
//!
//! (B)/(C) are stated at the CALLER's fixed `c` — they must be, since the
//! caller supplies `hac`/`uac`/`hcb`/`ucb` once. (D)'s split point is
//! `c_k := a + ofNat(succ m_ac) · delta_of(a, b, combined)`, computed from the
//! mesh counts actually used at the current accuracy, hence a fresh `Nat`
//! arithmetic expression at every `e` and never definitionally `c`. There is
//! nowhere to put a shared literal: `c_k` is *derived from* `m_ac`/`m_cb`, and
//! those are exactly what must grow without bound.
//!
//! **But what is missing is `Equiv (riemannSum F a c_k m_ac) (riemannSum F a c
//! m_ac)`, a `riemannSum` fact — not `integral F a c_k … ` versus `integral F
//! a c …`.** The FIFTEENTH lane's entry above reached for
//! `integral_congr_endpoint` and sized it against
//! [`declare_integral_witness_independent`]'s `Converges`/
//! `riemann_sum_deep_cauchy_cross` route. That is the wrong (and larger)
//! lemma: the two `integral`s never have to be compared at all, because (B)
//! and (C) already relate the caller's `c`-integrals to `c`-Riemann sums, and
//! only the SUMS need bridging.
//!
//! **And the FIFTEENTH lane's argument that a `riemannSum`-level congruence is
//! impossible "even in principle" is wrong.** It reads: "`riemannSum`'s value
//! at a sample index is a RATIONAL (`sample x n`), and two `Equiv` `CReal`s
//! are only guaranteed to agree in the LIMIT, never sample-by-sample". True,
//! and it rules out proving the congruence *sample by sample* — which nothing
//! requires. `riemannSum F x y m` is `sumRange` of `mul (F (add x (mul (ofNat
//! i) Δ))) Δ`, a `CReal` built compositionally out of `add`/`mul`/`ofNat`, so
//! the congruence follows from the setoid's own congruence lemmas without
//! `sample` appearing anywhere.
//!
//! [`riemann_sum_congr_endpoints`] is that proof, **kernel-accepted on the
//! first attempt**, symbolic in `F`, the outer interval `[aa, bb]`, its
//! `UniformlyContinuousOn` witness, both endpoint pairs and the mesh count,
//! closed into a real `Theorem` over all of them and stated at the [`rsum`]
//! type rather than the `sumRange` type its term builds (so the test also
//! pins that the two are one `Definition` body at one hash-consed `ExprId`).
//! Every step names an existing lemma:
//! [`CRealPrelude::neg_congr`]/[`CRealPrelude::add_congr`]/
//! [`CRealPrelude::mul_congr`] for `Equiv Δ Δ'` and the sample points,
//! [`CRealPrelude::riemann_sample_in_bounds`] plus two
//! [`CRealPrelude::le_trans`] to place both sample points in `[aa, bb]`,
//! [`CRealPrelude::congr_of_uniformly_continuous`] for `Equiv (F pt) (F pt')`
//! (which exists precisely because a global congruence is unavailable for an
//! `F` continuous only on `[aa, bb]`), and [`sum_range_congr_lt_proof`] — the
//! `Nat.lt`-BOUNDED sum congruence, for the same reason
//! [`declare_riemann_sum_split_exact_of_uc`] uses the bounded one.
//!
//! It varies BOTH endpoints at once, which is what the combine needs: `[a,
//! c_k] → [a, c]` moves the right endpoint and `[c_k, b] → [c, b]` moves the
//! left, and one lemma covers both.
//!
//! **`Equiv c_k c` is available exactly when the mesh family is the
//! multiplicative one.** [`CRealPrelude::riemann_sum_split_scale_invariant`]
//! proves `Equiv c_k c_0` for the [`succ_mul_succ`] family and for no other,
//! so Gap A's resolution is a PREREQUISITE for Gap B's, not an independent
//! item: with [`mesh_count_align`]'s additive padding there is no `c_0` to be
//! `Equiv` to. `integral_split` would therefore be stated with `c` bound to
//! the base split point `c_0` of a caller-chosen rational proportion
//! `(m_ac0, m_cb0)`, not with `c` universally quantified.
//!
//! **What remains, and it is now only the combine.** Both prerequisites the
//! FIFTEENTH lane named are landed and kernel-checked. The remaining volume is
//! the TWELFTH lane's own estimate, unchanged: three `riemann_sum_integral_close`
//! applications, [`close_within_of_within_indexed`] to move each `Within` to a
//! `CReal.le (abs …)`, [`bnd_leg_plus_share_le_at`] once per leg to weaken the
//! bounds to a common `natDivSucc`, `abs_add_le` twice for the three-way
//! triangle, `le_congr` to substitute
//! [`CRealPrelude::riemann_sum_split_exact_of_uc`]'s exact identity (now
//! composed with [`riemann_sum_congr_endpoints`] on each of its two summands),
//! and `equiv_zero_of_small` to close, with `big_n`/`e_inner` chosen as
//! explicit functions of `e`. NOT attempted here: this lane's budget covered
//! resolving the two gaps with the compile-and-verify cadence, not the combine
//! on top of them, and writing ~450 unverified lines is what failed eleven
//! times before.
//!
//! [`mesh_count_align_mul`], [`riemann_sum_congr_endpoints`],
//! [`nat_le_add_left`] and [`le_dest_elim`] are all private helpers with their
//! own `#[cfg(test)]` modules, wired into no `CRealPrelude` field, no
//! `BuildStep`, no `EXPECTED_STEP_ORDER` entry and no inventory shard row;
//! `creal_prelude_builds` is unaffected.
//!
//! ## `CReal.integral_split` — the two gap resolutions COMPOSE, checked:
//! [`split_identity_at_equiv_point`] (SIXTEENTH lane, same day)
//!
//! Rather than assert that Gap A's and Gap B's resolutions fit together, this
//! is the join, kernel-checked: `Equiv (riemannSum F a b combined) (add
//! (riemannSum F a c m_ac) (riemannSum F c b m_cb))` — the exact identity
//! [`CRealPrelude::riemann_sum_split_exact_of_uc`] proves, RESTATED AT THE
//! CALLER'S OWN `c`, given only `Equiv c_k c`. Two
//! [`riemann_sum_congr_endpoints`] applications (one moving the right
//! endpoint, one the left, which is why that helper varies both), combined by
//! [`CRealPrelude::add_congr`] and chained onto the split identity.
//!
//! This is the shape the combine consumes: the three
//! `riemann_sum_integral_close` legs are stated at the caller's fixed `c`,
//! and now so is the split identity, so nothing downstream ever mentions
//! `c_k`.
//!
//! **The kernel rejected the first version, and the mistake is worth
//! recording because the message named nothing relevant.**
//! [`riemann_sum_congr_endpoints`] takes the outer interval `(aa, bb)` — the
//! one its `UniformlyContinuousOn` witness is *about* — separately from the
//! sub-interval endpoints it is moving. The `[c_k, b]` leg was given
//! `(aa, bb) := (c_k, b)`, reading the leg's own sub-interval as the
//! witness's interval; `u` witnesses continuity on `[a, b]` and on nothing
//! else. The rejection was a bare `TypeMismatch` between two `ExprId`s,
//! mentioning neither `u` nor `c_k`, and it is indistinguishable from a
//! transposed endpoint pair or a backwards `Equiv` — this file's most common
//! failure family. **Both legs take `(a, b)`.** Fixed and accepted; the
//! `[a, c_k]` leg had it right from the start, which is exactly why a helper
//! that varies both endpoints needs a caller test that exercises both
//! directions.
//!
//! What remains for `integral_split` itself, unchanged: three
//! `riemann_sum_integral_close` applications,
//! [`close_within_of_within_indexed`] per leg,
//! [`bnd_leg_plus_share_le_at`] per leg, `abs_add_le` twice, and
//! `equiv_zero_of_small` to close, with `big_n`/`e_inner` as explicit
//! functions of `e`. Not attempted here.
//!
//! ## `CReal.integral_split` — PROVED 2026-08-27 (a SEVENTEENTH lane), and
//! the remaining volume was NOT what four sizings said it was
//!
//! [`CRealPrelude::integral_split`] is admitted, axiom-free, registered:
//!
//! ```text
//! ∀ F a b (m_ac0 m_cb0 : Nat) (hab : le a b) (u : UniformlyContinuousOn F a b)
//!   (hac : le a c) (hcb : le c b)
//!   (uac : UniformlyContinuousOn F a c) (ucb : UniformlyContinuousOn F c b),
//!     Equiv (integral F a b hab u)
//!           (add (integral F a c hac uac) (integral F c b hcb ucb))
//!   where c := add a (mul (ofNat (succ m_ac0))
//!                         (delta_of a b (add (succ m_ac0) m_cb0)))
//! ```
//!
//! **No seventeenth gap appeared. The twelfth lane's volume estimate did not
//! hold either — it was an estimate of a DIFFERENT proof.** That plan (three
//! `riemann_sum_integral_close` legs,
//! [`CRealPrelude::close_within_of_within_indexed`] and
//! [`bnd_leg_plus_share_le_at`] per leg, `abs_add_le` twice,
//! `equiv_zero_of_small` to close, `big_n`/`e_inner` as functions of `e`)
//! routes the combine through a hand-built triangle inequality on `abs`.
//! **None of those five lemmas appears in the proof**, and `bnd_leg_plus_share_le_at`
//! and the CPS form of [`mesh_count_align_mul`] are still dead code because of
//! it.
//!
//! The route actually taken is [`declare_integral_add`]'s, one interval wider:
//! get every leg to a `Converges` fact at a shared mesh family, and the
//! combine is three named lemmas.
//!
//! ```text
//! conv_ab/ac/cb  leg_converges, three times
//! conv_sum       converges_add
//! cross          split_identity_at_equiv_point APPLIED at n -- `Equiv` IS the
//!                per-index `Within` at 2/(n+1) (`CReal.Equiv x y := ∀ n,
//!                Within (seq x n − seq y n) (2/(n+1))`), the same step
//!                `declare_converges_of_equiv` takes
//! step           converges_of_close at Kc := 2
//! final          converges_unique
//! ```
//!
//! So the entire rational estimate lives in ONE place, [`leg_converges`],
//! which is [`declare_integral_le`]'s own `step_f` with one generalization and
//! one new inequality:
//!
//! - **Generalization**: `declare_integral_le` calls
//!   [`CRealPrelude::riemann_sum_cauchy`] directly, which fixes the refinement
//!   at [`common_refinement`]'s own target. A split leg must reach whatever
//!   count the alignment hands it, so this calls
//!   [`CRealPrelude::riemann_sum_shared_accuracy_close`] at a FREE `k1` and
//!   transports onto the caller's mesh with one [`nat_rewrite_prop`] across
//!   [`le_dest_elim`]'s own equation.
//! - **New inequality**: `riemann_sum_shared_accuracy_close`'s bound carries
//!   `modulus(l, shift jj1)` for its internal `l`, while
//!   [`bnd_leg_plus_share_le`] folds only the all-at-one-index shape
//!   `modulus(idx, shift idx)`. At `oi = oj = jj1 = jj2 := n` those differ in
//!   exactly one leaf, closed by [`RatPrelude::nat_div_succ_antitone`](crate::RatPrelude::nat_div_succ_antitone)
//!   given `Nat.le n l` — and `l = succ_mul_succ(m2, m1).0 ≥ m1`
//!   ([`nat_le_add_left`]), so the caller's own `Nat.le n (M n)` suffices.
//!
//! **Two parameters the earlier plans left free are not free, and both are
//! forced by the construction rather than chosen.**
//!
//! - `c` is **not** universally quantified. The SIXTEENTH lane's Gap B entry
//!   already said why ([`CRealPrelude::riemann_sum_split_scale_invariant`]
//!   proves `Equiv c_k c_0` for the [`succ_mul_succ`] family and no other);
//!   this lane is where it becomes a signature. `c` is the base split point of
//!   the caller's proportion, built by [`split_point_base`] with the identical
//!   recipe that theorem's own `c_0` uses. Every rational proportion is
//!   reachable — `m_ac0`/`m_cb0` are free `Nat`s, and the test asserts the
//!   transposed proportion gives a DIFFERENT `CReal`, so the stratum is
//!   demonstrably not bisection-only.
//! - `big_n` is **not** free: [`leg_converges`] needs `Nat.le n (M n)` on
//!   every leg for the antitone step above, and
//!   [`mesh_count_align_mul_bounds`]'s scale factor is
//!   `((deep_ab + deep_ac) + deep_cb) + big_n`, so `big_n := n`.
//!
//! **`mesh_count_align_mul` was refactored, not duplicated.** Its scaling
//! argument and the six `Nat.le` facts move to
//! [`mesh_count_align_mul_bounds`]; the CPS wrapper calls it. A CPS helper
//! cannot serve [`leg_converges`], which runs its OWN [`le_dest_elim`] once
//! per leg at whichever mesh it is given, and needs the `Nat.le` facts as
//! plain terms.
//!
//! **Cost.** `creal_prelude_builds` moves from **31.55 s** (load 8.4) to
//! **39.70 s** (load 4.6) — matched A/B on this tree, the declaration disabled
//! and re-enabled between readings; a same-load pair at load ≈18.7 reads
//! 42.82 s → 78.00 s, which is what a contended box does to both numbers, not
//! an extra cost. Call it **+8 to +15 s**, landing the gate at the top edge of
//! its 29–39 s band. Bisected: a `leg_converges` at a SIMPLE mesh family
//! (`deep(n) + n`) costs **0.3 s**, so the cost is not the estimate machinery
//! but the size of the aligned mesh terms (`succ_mul_succ` over three
//! `deep_at` moduli) that all three legs and the cross are stated at. No
//! `CReal.integral` `Definition` is ever unfolded — every `integral` is a
//! shared `const_app` on both sides of every step, the discipline
//! `riemannSum_integral_close`'s own 74 s incident established.
//!
//! **Dead code went 7 → 4.** [`riemann_sum_congr_endpoints`],
//! [`split_identity_at_equiv_point`], [`nat_le_add_left`] and
//! [`le_dest_elim`] are now consumed by a real, kernel-verified declaration.
//! Still unconsumed, and NOT silenced: [`mesh_count_align`] (the additive
//! predecessor `mesh_count_align_mul` superseded), [`MeshAlignMul`] +
//! [`mesh_count_align_mul`] (the CPS form — this route uses the `_bounds`
//! form), and [`bnd_leg_plus_share_le_at`] (the independent-index variant —
//! this route runs every index at `n`, so the same-index
//! [`bnd_leg_plus_share_le`] suffices). Those four are the honest measure of
//! how far the shipped proof diverges from the plan that predicted them.
//!
//! ## `CReal.integral_split` at an ARBITRARY split point — checked 2026-08-27
//! (an EIGHTEENTH lane). The closing lane named ONE missing piece; there are
//! **two**, and the second one is not a proof gap at all — it is a
//! constructive obstruction that changes what the theorem's statement can be
//!
//! Starting point verified, not assumed: `git grep` for any close-endpoint
//! congruence (`close_endpoint`, `endpoints_close`, `congr_endpoints_close`)
//! over the whole of `creal/` returns **zero** hits, while
//! [`riemann_sum_congr_endpoints`] — the `Equiv` version — has **18**. So the
//! SEVENTEENTH lane's named obstruction is real and unbuilt, and the control
//! confirms the query is not simply misaimed.
//!
//! **Missing piece 1, as named by the closing lane and confirmed here: the
//! endpoint estimate at merely-close endpoints.** [`riemann_sum_split_exact`]
//! is exact only when the split point IS a mesh point, and
//! [`CRealPrelude::riemann_sum_split_scale_invariant`] pins the mesh-point
//! family to `c_0` EXACTLY, so for an arbitrary `c` the reachable mesh point
//! is only *close*. What is needed is
//!
//! ```text
//! |riemannSum F a c m − riemannSum F a c' m|  ≤  M·δ + (c'−a)·ω(δ),   δ := |c − c'|
//! ```
//!
//! uniformly in `m` — the `≤` analogue of [`riemann_sum_congr_endpoints`],
//! with each of that proof's congruence steps
//! ([`CRealPrelude::neg_congr`]/[`CRealPrelude::add_congr`]/
//! [`CRealPrelude::mul_congr`] and
//! [`CRealPrelude::congr_of_uniformly_continuous`]) replaced by a
//! triangle-inequality estimate and `sum_range_congr_lt_proof` replaced by
//! [`CRealPrelude::abs_sum_range_le`]/[`CRealPrelude::sum_range_le`]. The
//! term-by-term shape is
//! `|F(p_i)Δ − F(p'_i)Δ'| ≤ |F(p_i)|·|Δ−Δ'| + Δ'·ω(|p_i − p'_i|)` with
//! `|p_i − p'_i| = i·|Δ−Δ'| ≤ δ`, summed over `m+1` terms — so the `m`
//! cancels and the bound is uniform in the mesh count, which is what lets
//! [`CRealPrelude::riemann_sum_integral_close`] carry it to the integrals.
//!
//! **Missing piece 2, which no register entry states and which the
//! "endpoint estimate" framing hides: even with piece 1 in hand, an
//! arbitrary `c` cannot be LOCATED in the proportion family without a
//! positivity witness on `b − a`.** [`CRealPrelude::integral_split`]'s split
//! point is `a + q·(b−a)` for the rational proportion
//! `q := succ(m_ac0)/(succ(m_ac0)+succ(m_cb0))`. Hitting an arbitrary `c`
//! within `δ` requires approximating `t := (c−a)/(b−a)`, i.e. **dividing by
//! `b − a`**, and `CReal.inv` ([`super::inverse`]) takes a `PosBound`
//! argument. `hab : le a b` is non-strict, so `b − a` is not known positive
//! and `t` is not constructible. This is the same wall the FOURTH and FIFTH
//! lanes hit from the `crossingIndex` side — `crossing.rs`'s step parameter
//! is a `Rat` and the mesh step `(b−a)/(m+1)` is a `CReal` — but stated at
//! the level where it is actionable rather than as a signature mismatch.
//!
//! Consequences, and they are the useful part:
//!
//! - The next stratum in the ADR-0603 sense is **not** "`c` universally
//!   quantified". It is `integral_split` at arbitrary `c` **given a
//!   `PosBound` on the interval width** — a genuine strengthening of the
//!   landed dense-proportion form, and the form FTC actually consumes (`G(x)
//!   := integral F a x`; the split of `[a, x+h]` at `x` has a nondegenerate
//!   `[x, x+h]` in hand at every point where the derivative estimate is
//!   taken).
//! - The hypothesis is removable, but by a **case split, not an estimate**:
//!   a cotransitivity step decides, per accuracy `e`, either
//!   `b − a < 1/(e+1)` (in which case all three integrals are within
//!   `M/(e+1)` of `0` by the width bound below, and the identity holds at
//!   that accuracy for free) or `b − a > 1/(2e+2)` (in which case `CReal.inv`
//!   is available). `equiv_zero_of_small` consumes one accuracy at a time, so
//!   the case split is legal exactly where it is needed. Not attempted here;
//!   named so the next lane does not re-derive that arbitrary-`c` is blocked
//!   and stop there, which is what the plain reading of piece 2 invites.
//!
//! **What was built this lane, and why this and not a slice of piece 1**:
//! the previous lane's own closing lesson is that four sizings all failed
//! because none asked *which declaration in this file already relates two
//! integrals under a bound*. Asking that question here gives
//! [`CRealPrelude::integral_le`] + [`CRealPrelude::integral_const`], and they
//! compose immediately into the width bound
//!
//! ```text
//! CReal.integral_abs_le : ∀ F a b k hab u, BoundedOn F a b k →
//!   le (abs (integral F a b hab u))
//!      (mul (ofRat (natDivSucc (succ k) 0)) (add b (neg a)))
//! ```
//!
//! — the `M·(b−a)` bound. It is on the critical path for BOTH pieces: it is
//! piece 1's own `M·δ` leaf (the `|F(p_i)|·|Δ−Δ'|` term), and it is exactly
//! what discharges the degenerate branch of piece 2's cotransitivity split.
//! It is also what FTC needs directly for the antiderivative's own
//! continuity (`|G(y) − G(x)| ≤ M·|y − x|`).

use super::completeness::half_shift_le;
use super::convergence::{
    converges_applied, converges_predicate, div_succ_at, exists_intro, exists_ty,
};
use super::ring_helpers::right_distrib;
use super::series::{chain_within3, within_symm};
use super::{
    CRealPrelude, DERIVED_HEIGHT, and_intro, cadd, creal_ty, div_succ, embed, equiv, halves,
    modulus, sample, shift, weaken, within,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{
    nat_eq_to_rat, nat_rewrite_prop, normalize, one_le_succ, radd, rat_eq_rewrite, rat_ty, rchain,
    rcongr, req, rle, rmul, rneg, rone, rsymm, rtrans, rzero,
};

/// Delta height for `CReal.riemannSum`: above `CReal.sumRange`
/// (`DERIVED_HEIGHT + 41`) and `CReal.ofNat` (`DERIVED_HEIGHT + 14`), the two
/// definitions it is built from.
const RIEMANN_HEIGHT: u16 = DERIVED_HEIGHT + 45;

/// Admit `CReal.riemannSum`, `CReal.riemannSum_add`, `CReal.mul_riemannSum`
/// and `CReal.riemannSum_le`. See the module documentation for what is and
/// is not covered.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_integral(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_of_nat_le(d, p)?;
    declare_riemann_sum(d, p)?;
    declare_riemann_sum_add(d, p)?;
    declare_mul_riemann_sum(d, p)?;
    declare_riemann_sum_le(d, p)?;
    declare_riemann_sample_in_bounds(d, p)?;
    declare_riemann_sum_le_on(d, p)?;
    declare_riemann_sum_const(d, p)?;
    declare_mesh_le_of_ge(d, p)?;
    declare_mesh_scaled_le_of_ge(d, p)
}

// --- shared term builders ----------------------------------------------------

/// `CReal -> CReal`.
fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.le, &[x, y])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `add b (neg a)` — the interval width `b − a`.
fn width_of(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    cadd(d, p, b, na)
}

/// `mul (add b (neg a)) (ofRat (Rat.natDivSucc 1 m))` — the mesh
/// `Δ = (b − a)/(m + 1)`. Total in `m`: see the module documentation for why
/// no `CReal.inv`/`PosBound` is needed.
fn delta_of(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, m: ExprId) -> ExprId {
    let width = width_of(d, p, a, b);
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_real = embed(d, p, frac);
    cmul(d, p, width, frac_real)
}

/// `add a (mul (ofNat i) delta)` — the `i`-th LEFT sample point `a + i·Δ`.
fn sample_point(
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

/// `fun i => mul (f (sample_point a delta i)) delta` — the `i`-th Riemann
/// term, `f(a + i·Δ)·Δ`. Built as its own helper (rather than inlined at
/// each call site) so every occurrence — inside `riemannSum`'s own
/// definition and inside every theorem about it — is the *same* term,
/// minimizing what the kernel's defeq check has to bridge.
fn summand_fn(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, a: ExprId, delta: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let sp = sample_point(d, p, a, delta, i);
    let fx = d.apply(f, &[sp]);
    let term = cmul(d, p, fx, delta);
    d.lam_fv(i_fv, nat, term)
}

/// `CReal.riemannSum f a b m`.
fn rsum(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, a: ExprId, b: ExprId, m: ExprId) -> ExprId {
    d.const_app(p.riemann_sum, &[f, a, b, m])
}

// --- `CReal.ofNat_le` -----------------------------------------------------

/// `CReal.ofNat_le : ∀ i j : Nat, Nat.le i j → CReal.le (ofNat i) (ofNat j)`
/// — `CReal.ofNat` is monotone.
///
/// `CReal.ofNat n := CReal.ofRat (Rat.natDivSucc n 0)` ([`super::archimedean`]),
/// so this is [`RatPrelude::nat_div_succ_le_add_left`]
/// (`∀ a e j, Rat.le (natDivSucc a j) (natDivSucc (a+e) j)` — monotone in the
/// numerator, stated additively so no `Nat`-subtraction ever appears) lifted
/// across [`CRealPrelude::of_rat_le`], then transported from the existential
/// witness `Nat.le_dest` supplies (`i + k = j`) up to the actual bound `j`.
///
/// The same idiom as `series.rs`'s `sumRange_tail_within_le`: `Nat.le_dest i j
/// hij : Exists (fun k => Eq Nat (add i k) j)`; applying
/// `nat_div_succ_le_add_left` at `(i, k, 0)` gives exactly this theorem's
/// conclusion *shape*, but indexed at `add i k` rather than `j`, and one
/// `Nat`-equality transport ([`nat_rewrite_prop`]) carries it over.
fn declare_of_nat_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_add = d.prelude().add;
    let nat_le_dest = d.prelude().le_dest;

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let hle_ty = d.le(i, j);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let of_nat_i = d.const_app(p.of_nat, &[i]);
    // target_at(x) := CReal.le (ofNat i) (ofNat x) -- this theorem's
    // conclusion at x := j, and `nat_div_succ_le_add_left`'s shape at
    // x := add i k.
    let target_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let of_nat_x = d.const_app(p.of_nat, &[x]);
        cle(d, p, of_nat_i, of_nat_x)
    };
    let target = target_at(d, j);

    // pred := λ k, Eq Nat (add i k) j.
    let pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sum = d.const_app(nat_add, &[i, k]);
        let body = d.eq(sum, j);
        d.lam_fv(k_fv, nat, body)
    };

    let represented = d.const_app(nat_le_dest, &[i, j, hle]);

    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let i_plus_k = d.const_app(nat_add, &[i, k]);
        let e_ty = d.eq(i_plus_k, j);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        // body_at_ik : CReal.le (embed (natDivSucc i 0)) (embed (natDivSucc
        // (add i k) 0)) -- defeq target_at(add i k), since `ofNat n` unfolds
        // to `embed (natDivSucc n 0)`.
        let zero_nat = d.num(0);
        let rat_i = d.const_app(p.rat.nat_div_succ, &[i, zero_nat]);
        let rat_ik = d.const_app(p.rat.nat_div_succ, &[i_plus_k, zero_nat]);
        let rat_le = d.lemma(p.rat.nat_div_succ_le_add_left, &[i, k, zero_nat]);
        let body_at_ik = d.lemma(p.of_rat_le, &[rat_i, rat_ik, rat_le]);

        let rewritten = nat_rewrite_prop(d, i_plus_k, j, e, body_at_ik, &target_at);
        let with_e = d.lam_fv(e_fv, e_ty, rewritten);
        d.lam_fv(k_fv, nat, with_e)
    };

    let proof_body = exists_elim(d, pred, target, represented, minor);

    let ty = {
        let after_hle = d.arrow(hle_ty, target);
        let over_j = d.pi_fv(j_fv, nat, after_hle);
        d.pi_fv(i_fv, nat, over_j)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, proof_body);
        let over_j = d.lam_fv(j_fv, nat, with_hle);
        d.lam_fv(i_fv, nat, over_j)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_nat_le,
        uparams: vec![],
        ty,
        value,
    })
}

// --- mesh-count alignment (resolves the TWELFTH lane's `integral_split` gap) ---

/// Resolves the mesh-count alignment gap the TWELFTH lane's module-doc entry
/// diagnoses ("`CReal.integral_split` — checked 2026-08-27"): given three
/// independently-shaped moduli `deep_ab`, `deep_ac`, `deep_cb : Nat` (e.g.
/// each a different `deep(F,·,·,u,e)` uniform-continuity modulus) and a free
/// `big_n : Nat`, derives the EXISTENCE of a `depth_ab : Nat` with
/// `Eq Nat (add deep_ab depth_ab) combined`, where
/// `combined := add (succ (add deep_ac depth_ac)) (add deep_cb depth_cb)`
/// and `depth_ac := depth_cb := add(deep_ab, big_n)` — the literal
/// `m_ac`/`m_cb`/`combined` shape
/// [`CRealPrelude::riemann_sum_split_exact_of_uc`]'s own identity needs — via
/// `Nat.le_dest` + `exists_elim`, **never `Nat.sub`** (the naive
/// `depth_ab := combined - deep_ab` is exactly the truncation trap this
/// module's kernel-facts list warns about, since nothing bounds
/// `deep_ab ≤ combined` a priori without the `le` chain built below).
///
/// Continuation-passing rather than returning `(depth_ab, proof)` directly:
/// `Nat.le_dest`'s witness cannot escape its own elimination scope
/// ([`declare_of_nat_le`]'s own idiom, reused verbatim here), so a caller
/// needing a further fact ABOUT `depth_ab` (e.g. transporting a
/// `riemann_sum_integral_close` application built generically at a bound
/// depth across the equation via [`nat_rewrite_prop`]) supplies `build`,
/// invoked with the bound `depth_ab` and the equation proof, and must
/// return a proof of the caller-fixed `target` (which therefore must not
/// mention `depth_ab`, exactly [`exists_elim`]'s own precondition).
///
/// The `Nat.le deep_ab combined` premise `Nat.le_dest` needs is a four-hop
/// `le_trans` chain over EXISTING lemmas only, no `add_assoc`/`add_right_comm`
/// reassociation anywhere:
///
/// 1. `Nat.le_add_right(deep_ab, big_n) : Le deep_ab (add deep_ab big_n)`
///    — literally `Le deep_ab depth_ac`, no rewrite needed.
/// 2. `Nat.le_add_right(depth_ac, deep_ac) : Le depth_ac (add depth_ac deep_ac)`,
///    transported across `Nat.add_comm(depth_ac, deep_ac)` via
///    [`nat_rewrite_prop`] to `Le depth_ac (add deep_ac depth_ac)` — literally
///    `Le depth_ac m_ac`.
/// 3. `Nat.le_trans` composes 1 and 2 into `Le deep_ab m_ac`.
/// 4. `Nat.le_succ(m_ac) : Le m_ac (succ m_ac)`, composed by `Nat.le_trans`
///    into `Le deep_ab (succ m_ac)`.
/// 5. `Nat.le_add_right(succ m_ac, m_cb) : Le (succ m_ac) (add (succ m_ac) m_cb)`
///    — literally `Le (succ m_ac) combined` — composed by `Nat.le_trans`
///    into the final `Le deep_ab combined`.
pub(super) fn mesh_count_align(
    d: &mut IntDev<'_>,
    deep_ab: ExprId,
    deep_ac: ExprId,
    deep_cb: ExprId,
    big_n: ExprId,
    target: ExprId,
    build: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let np = d.prelude();
    let nat = d.nat_ty();

    // depth_ac := depth_cb := add(deep_ab, big_n) -- baked into both child
    // depths so `deep_ab` is available inside `combined` as a term, per the
    // TWELFTH lane's resolution.
    let depth_ac = NatOps::add(d, deep_ab, big_n);
    let m_ac = NatOps::add(d, deep_ac, depth_ac);
    let m_cb = NatOps::add(d, deep_cb, depth_ac);
    let succ_m_ac = d.succ(m_ac);
    let combined = NatOps::add(d, succ_m_ac, m_cb);

    // h1 : Le deep_ab depth_ac.
    let h1 = d.lemma(np.le_add_right, &[deep_ab, big_n]);

    // h2 : Le depth_ac m_ac.
    let h2a = d.lemma(np.le_add_right, &[depth_ac, deep_ac]);
    let depth_ac_plus_deep_ac = NatOps::add(d, depth_ac, deep_ac);
    let comm = d.lemma(np.add_comm, &[depth_ac, deep_ac]);
    let h2 = nat_rewrite_prop(d, depth_ac_plus_deep_ac, m_ac, comm, h2a, &|d, x| {
        d.le(depth_ac, x)
    });

    // h3 : Le deep_ab m_ac.
    let h3 = d.lemma(np.le_trans, &[deep_ab, depth_ac, m_ac, h1, h2]);

    // h4 : Le m_ac succ_m_ac; h5 : Le deep_ab succ_m_ac.
    let h4 = d.lemma(np.le_succ, &[m_ac]);
    let h5 = d.lemma(np.le_trans, &[deep_ab, m_ac, succ_m_ac, h3, h4]);

    // h6 : Le succ_m_ac combined; h7 : Le deep_ab combined.
    let h6 = d.lemma(np.le_add_right, &[succ_m_ac, m_cb]);
    let h7 = d.lemma(np.le_trans, &[deep_ab, succ_m_ac, combined, h5, h6]);

    let represented = d.const_app(np.le_dest, &[deep_ab, combined, h7]);

    // pred := λ k, Eq Nat (add deep_ab k) combined.
    let pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sum = NatOps::add(d, deep_ab, k);
        let body = d.eq(sum, combined);
        d.lam_fv(k_fv, nat, body)
    };

    let minor = {
        let depth_ab_fv = d.fresh_fvar();
        let depth_ab = d.kernel().fvar(depth_ab_fv);
        let sum = NatOps::add(d, deep_ab, depth_ab);
        let e_ty = d.eq(sum, combined);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let body = build(d, depth_ab, e);
        let with_e = d.lam_fv(e_fv, e_ty, body);
        d.lam_fv(depth_ab_fv, nat, with_e)
    };

    exists_elim(d, pred, target, represented, minor)
}

#[cfg(test)]
mod mesh_count_align_tests {
    use super::*;
    use crate::Declaration;

    /// The raw existence claim, symbolic in all four inputs, closed into a
    /// real `Theorem` universally quantified over `deep_ab deep_ac deep_cb
    /// big_n : Nat` (mirroring [`declare_of_nat_le`]'s own final `pi_fv`/
    /// `lam_fv` wrapping -- the four moduli are genuinely free variables of
    /// [`mesh_count_align`]'s own construction, so `Kernel::infer` on the
    /// unwrapped proof alone rejects them as `UnboundFVar`, exactly as it
    /// would reject an unclosed term anywhere else in this file). `target :=
    /// pred`'s own `Exists`, `build` is plain `exists_intro`. Confirms
    /// [`mesh_count_align`]'s proof is accepted by `Kernel::add_declaration`
    /// itself, not merely by `cargo check`.
    #[test]
    fn mesh_count_align_proves_the_stated_existence() {
        crate::on_a_deep_stack(mesh_count_align_proves_the_stated_existence_body);
    }

    fn mesh_count_align_proves_the_stated_existence_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();

        let deep_ab_fv = d.fresh_fvar();
        let deep_ab = d.kernel().fvar(deep_ab_fv);
        let deep_ac_fv = d.fresh_fvar();
        let deep_ac = d.kernel().fvar(deep_ac_fv);
        let deep_cb_fv = d.fresh_fvar();
        let deep_cb = d.kernel().fvar(deep_cb_fv);
        let big_n_fv = d.fresh_fvar();
        let big_n = d.kernel().fvar(big_n_fv);

        // Reconstruct `combined` independently, mirroring
        // `mesh_count_align`'s own construction, so a defect in ITS
        // construction (not just a matching bug in this test) is what the
        // kernel's type-check would catch.
        let depth_ac = NatOps::add(&mut d, deep_ab, big_n);
        let m_ac = NatOps::add(&mut d, deep_ac, depth_ac);
        let m_cb = NatOps::add(&mut d, deep_cb, depth_ac);
        let succ_m_ac = d.succ(m_ac);
        let combined = NatOps::add(&mut d, succ_m_ac, m_cb);

        let pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sum = NatOps::add(&mut d, deep_ab, k);
            let body = d.eq(sum, combined);
            d.lam_fv(k_fv, nat, body)
        };
        let target = exists_ty(&mut d, p, nat, pred);
        let build = |d: &mut IntDev<'_>, depth_ab: ExprId, e: ExprId| -> ExprId {
            exists_intro(d, p, nat, pred, depth_ab, e)
        };

        let proof = mesh_count_align(&mut d, deep_ab, deep_ac, deep_cb, big_n, target, &build);

        // Close over the four free `Nat` variables, outermost-first
        // `deep_ab`, matching the argument order `mesh_count_align` itself
        // takes.
        let ty = {
            let over_big_n = d.pi_fv(big_n_fv, nat, target);
            let over_cb = d.pi_fv(deep_cb_fv, nat, over_big_n);
            let over_ac = d.pi_fv(deep_ac_fv, nat, over_cb);
            d.pi_fv(deep_ab_fv, nat, over_ac)
        };
        let value = {
            let over_big_n = d.lam_fv(big_n_fv, nat, proof);
            let over_cb = d.lam_fv(deep_cb_fv, nat, over_big_n);
            let over_ac = d.lam_fv(deep_ac_fv, nat, over_cb);
            d.lam_fv(deep_ab_fv, nat, over_ac)
        };

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "meshCountAlignStatedExistenceSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "mesh_count_align must prove the stated existence, closed over all four inputs: {:?}",
            result.err()
        );
    }

    /// Non-vacuity: swapping `deep_ac`/`deep_cb` must produce a DIFFERENT
    /// `combined` -- the `succ` in `combined := add(succ(m_ac), m_cb)` binds
    /// only the `deep_ac` side, so the construction is not accidentally
    /// symmetric in its two child moduli. If this rendered identically, the
    /// positive test above would still pass while `mesh_count_align` ignored
    /// which modulus is which.
    #[test]
    fn mesh_count_align_is_not_symmetric_in_ac_and_cb() {
        crate::on_a_deep_stack(mesh_count_align_is_not_symmetric_in_ac_and_cb_body);
    }

    fn mesh_count_align_is_not_symmetric_in_ac_and_cb_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();

        let deep_ab_fv = d.fresh_fvar();
        let deep_ab = d.kernel().fvar(deep_ab_fv);
        let deep_ac_fv = d.fresh_fvar();
        let deep_ac = d.kernel().fvar(deep_ac_fv);
        let deep_cb_fv = d.fresh_fvar();
        let deep_cb = d.kernel().fvar(deep_cb_fv);
        let big_n_fv = d.fresh_fvar();
        let big_n = d.kernel().fvar(big_n_fv);

        let render_target_for = |d: &mut IntDev<'_>, ac: ExprId, cb: ExprId| -> String {
            let depth = NatOps::add(d, deep_ab, big_n);
            let m_ac = NatOps::add(d, ac, depth);
            let m_cb = NatOps::add(d, cb, depth);
            let succ_m_ac = d.succ(m_ac);
            let combined = NatOps::add(d, succ_m_ac, m_cb);
            let pred = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sum = NatOps::add(d, deep_ab, k);
                let body = d.eq(sum, combined);
                d.lam_fv(k_fv, nat, body)
            };
            let target = exists_ty(d, p, nat, pred);
            d.kernel().render_lean(target)
        };

        let straight = render_target_for(&mut d, deep_ac, deep_cb);
        let swapped = render_target_for(&mut d, deep_cb, deep_ac);
        assert_ne!(
            straight, swapped,
            "swapping deep_ac/deep_cb must change `combined`'s rendered target"
        );
    }

    /// Concrete instantiation: `deep_ab := 3`, `deep_ac := 5`, `deep_cb := 7`,
    /// `big_n := 2`, so `depth_ac = depth_cb = 5`, `m_ac = 10`, `m_cb = 12`,
    /// `combined = succ(10) + 12 = 23`, and the derived `depth_ab` must
    /// satisfy `3 + depth_ab = 23` -- i.e. `depth_ab = 20`, though this test
    /// checks the STATEMENT (via `Kernel::infer` against an independently
    /// reconstructed target), not a hand-computed witness, since
    /// `mesh_count_align` derives existence rather than the value.
    #[test]
    fn mesh_count_align_applies_at_three_five_seven_two() {
        crate::on_a_deep_stack(mesh_count_align_applies_at_three_five_seven_two_body);
    }

    fn mesh_count_align_applies_at_three_five_seven_two_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();

        let deep_ab = d.num(3);
        let deep_ac = d.num(5);
        let deep_cb = d.num(7);
        let big_n = d.num(2);

        let depth_ac = NatOps::add(&mut d, deep_ab, big_n);
        let m_ac = NatOps::add(&mut d, deep_ac, depth_ac);
        let m_cb = NatOps::add(&mut d, deep_cb, depth_ac);
        let succ_m_ac = d.succ(m_ac);
        let combined = NatOps::add(&mut d, succ_m_ac, m_cb);
        let expected_combined = d.num(23);
        assert!(
            d.kernel().def_eq(combined, expected_combined),
            "combined must reduce to the literal 23 at (3,5,7,2): got {}",
            d.kernel().render_lean(combined)
        );

        let pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sum = NatOps::add(&mut d, deep_ab, k);
            let body = d.eq(sum, combined);
            d.lam_fv(k_fv, nat, body)
        };
        let target = exists_ty(&mut d, p, nat, pred);
        let build = |d: &mut IntDev<'_>, depth_ab: ExprId, e: ExprId| -> ExprId {
            exists_intro(d, p, nat, pred, depth_ab, e)
        };

        let proof = mesh_count_align(&mut d, deep_ab, deep_ac, deep_cb, big_n, target, &build);

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "meshCountAlignThreeFiveSevenTwoSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: target,
            value: proof,
        });
        assert!(
            result.is_ok(),
            "mesh_count_align must apply at (3,5,7,2): {:?}",
            result.err()
        );
    }
}

// --- ratio-preserving (MULTIPLICATIVE) mesh-count alignment ---------------
//
// Resolves Gap A of this module's SIXTEENTH `integral_split` entry:
// [`mesh_count_align`]'s additive padding pins the split ratio at the
// midpoint, and takes no ratio argument at all. The helpers below realign the
// same three accuracy thresholds through [`succ_mul_succ`] instead, which
// leaves an arbitrary base ratio `(m_ac0, m_cb0)` EXACTLY fixed at every
// scale -- the same family [`CRealPrelude::riemann_sum_split_scale_invariant`]
// already proves `Equiv c_k c_0` for.

/// `Nat.le n (Nat.add k n)` — the prelude has `le_add_right` (`Le n (add n
/// k)`) but no `le_add_left`, so this is that lemma transported across
/// [`crate::nat_prelude::NatPrelude::add_comm`] via [`nat_rewrite_prop`],
/// exactly the idiom [`mesh_count_align`]'s own `h2` step already uses for
/// the same reason.
fn nat_le_add_left(d: &mut IntDev<'_>, k: ExprId, n: ExprId) -> ExprId {
    let np = d.prelude();
    let h = d.lemma(np.le_add_right, &[n, k]); // Le n (add n k)
    let n_plus_k = NatOps::add(d, n, k);
    let k_plus_n = NatOps::add(d, k, n);
    let comm = d.lemma(np.add_comm, &[n, k]); // Eq (add n k) (add k n)
    nat_rewrite_prop(d, n_plus_k, k_plus_n, comm, h, &|d, x| d.le(n, x))
}

/// From `hle : Nat.le base total`, bind a `depth : Nat` together with
/// `Eq Nat (add base depth) total` for the rest of a proof — `Nat.le_dest`
/// plus [`exists_elim`], **never `Nat.sub`** (the truncation trap this
/// module's kernel-facts list warns about).
///
/// Continuation-passing for the same reason [`mesh_count_align`] is:
/// `Nat.le_dest`'s witness cannot escape its own elimination scope, so
/// `target` must not mention `depth` ([`exists_elim`]'s own precondition).
/// Factored out of [`mesh_count_align`]'s own tail so
/// [`mesh_count_align_mul`] can nest three of them without repeating the
/// `pred`/`minor` boilerplate three times.
fn le_dest_elim(
    d: &mut IntDev<'_>,
    base: ExprId,
    total: ExprId,
    hle: ExprId,
    target: ExprId,
    build: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let np = d.prelude();
    let nat = d.nat_ty();
    let represented = d.const_app(np.le_dest, &[base, total, hle]);
    let pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sum = NatOps::add(d, base, k);
        let body = d.eq(sum, total);
        d.lam_fv(k_fv, nat, body)
    };
    let minor = {
        let depth_fv = d.fresh_fvar();
        let depth = d.kernel().fvar(depth_fv);
        let sum = NatOps::add(d, base, depth);
        let e_ty = d.eq(sum, total);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let body = build(d, depth, e);
        let with_e = d.lam_fv(e_fv, e_ty, body);
        d.lam_fv(depth_fv, nat, with_e)
    };
    exists_elim(d, pred, target, represented, minor)
}

/// The mesh counts and the three `Nat.le_dest` decompositions
/// [`mesh_count_align_mul`] hands its continuation.
///
/// `m_ac`/`m_cb`/`combined` are the terms the caller must build its three
/// `riemann_sum_integral_close` applications and its
/// [`CRealPrelude::riemann_sum_split_exact_of_uc`] application at;
/// `depth_X`/`eq_X` are what let a `riemann_sum_integral_close` application
/// built generically at a bound depth be transported onto them via
/// [`nat_rewrite_prop`].
#[derive(Clone, Copy)]
pub(super) struct MeshAlignMul {
    /// `succ_mul_succ(m_ac0, k).0` — the scaled `[a, c]` mesh count.
    pub m_ac: ExprId,
    /// `succ_mul_succ(m_cb0, k).0` — the scaled `[c, b]` mesh count.
    pub m_cb: ExprId,
    /// `add (succ m_ac) m_cb` — `riemann_sum_split_exact_of_uc`'s own
    /// combined `[a, b]` count.
    pub combined: ExprId,
    /// Bound witness of `Eq Nat (add deep_ab depth_ab) combined`.
    pub depth_ab: ExprId,
    /// That equation.
    pub eq_ab: ExprId,
    /// Bound witness of `Eq Nat (add deep_ac depth_ac) m_ac`.
    pub depth_ac: ExprId,
    /// That equation.
    pub eq_ac: ExprId,
    /// Bound witness of `Eq Nat (add deep_cb depth_cb) m_cb`.
    pub depth_cb: ExprId,
    /// That equation.
    pub eq_cb: ExprId,
}

/// The RATIO-PRESERVING replacement for [`mesh_count_align`], resolving
/// Gap A of this module's SIXTEENTH `integral_split` documentation entry.
///
/// Given the three uniform-continuity moduli `deep_ab`, `deep_ac`, `deep_cb`,
/// a **base ratio** `(m_ac0, m_cb0)` (which [`mesh_count_align`] has no
/// parameter for at all), and a free `big_n : Nat`, this scales BOTH sub-counts
/// by the single common factor
///
/// ```text
/// k := ((deep_ab + deep_ac) + deep_cb) + big_n
/// ```
///
/// through [`succ_mul_succ`], so `m_ac := succ_mul_succ(m_ac0, k).0` and
/// `m_cb := succ_mul_succ(m_cb0, k).0` satisfy `succ m_ac = succ(m_ac0)·succ k`
/// and `succ m_cb = succ(m_cb0)·succ k`. Since
/// [`declare_riemann_sum_split_exact`]'s split point is
/// `a + ofNat(succ m_ac) · (b − a)/(combined + 1)` and
/// `combined + 1 = succ m_ac + succ m_cb`, the split fraction is
///
/// ```text
/// succ(m_ac0)·succ k / ((succ(m_ac0) + succ(m_cb0))·succ k)
///   = succ(m_ac0) / (succ(m_ac0) + succ(m_cb0))
/// ```
///
/// — the `succ k` cancels identically, so the ratio is the caller's base
/// ratio at EVERY `k`, not merely in the limit. (That is the same family
/// [`CRealPrelude::riemann_sum_split_scale_invariant`] proves `Equiv c_k c_0`
/// for; this helper supplies the `Nat` side that theorem does not address —
/// which `k` makes all three accuracy thresholds clear at once.)
///
/// [`mesh_count_align`] gets `deep_ac ≤ m_ac` for free by *defining*
/// `m_ac := deep_ac + depth_ac`; that syntactic trick is exactly what forces
/// the additive shape, so it is unavailable here and all three thresholds
/// become obligations. All three reduce to ONE inequality:
///
/// ```text
/// succ_mul_succ(m0, k).0 = ((m0·k) + m0) + k  ≥  k     [nat_le_add_left]
/// ```
///
/// so `deep_ac ≤ k ≤ m_ac`, `deep_cb ≤ k ≤ m_cb`, and
/// `deep_ab ≤ k ≤ m_ac ≤ succ m_ac ≤ combined`, each a `le_trans` chain over
/// `le_add_right`/[`nat_le_add_left`]/`le_succ` only — no `add_assoc`, no
/// `Nat.sub`. The three [`le_dest_elim`] calls are then nested (outermost
/// `ab`, then `ac`, then `cb`), so `build` sees all three depths and all
/// three equations at once; `target` must mention none of them.
pub(super) fn mesh_count_align_mul(
    d: &mut IntDev<'_>,
    deep_ab: ExprId,
    deep_ac: ExprId,
    deep_cb: ExprId,
    m_ac0: ExprId,
    m_cb0: ExprId,
    big_n: ExprId,
    target: ExprId,
    build: &dyn Fn(&mut IntDev<'_>, MeshAlignMul) -> ExprId,
) -> ExprId {
    let b = mesh_count_align_mul_bounds(d, deep_ab, deep_ac, deep_cb, m_ac0, m_cb0, big_n);
    let MeshAlignMulBounds {
        m_ac,
        m_cb,
        combined,
        hle_ab,
        hle_ac,
        hle_cb,
        ..
    } = b;

    le_dest_elim(
        d,
        deep_ab,
        combined,
        hle_ab,
        target,
        &|d, depth_ab, eq_ab| {
            le_dest_elim(d, deep_ac, m_ac, hle_ac, target, &|d, depth_ac, eq_ac| {
                le_dest_elim(d, deep_cb, m_cb, hle_cb, target, &|d, depth_cb, eq_cb| {
                    build(
                        d,
                        MeshAlignMul {
                            m_ac,
                            m_cb,
                            combined,
                            depth_ab,
                            eq_ab,
                            depth_ac,
                            eq_ac,
                            depth_cb,
                            eq_cb,
                        },
                    )
                })
            })
        },
    )
}

/// The three scaled mesh counts and the six `Nat.le` facts about them, WITHOUT
/// the `Nat.le_dest` elimination [`mesh_count_align_mul`] wraps around them.
///
/// [`mesh_count_align_mul`] is continuation-passing because its consumer needs
/// the *depths*; [`leg_converges`] needs only the `Nat.le` facts (it runs its
/// own `le_dest_elim` internally, once per leg, at whichever mesh it is given),
/// and a CPS helper cannot supply those. Both callers share this body so the
/// scaling argument exists once.
#[derive(Clone, Copy)]
pub(super) struct MeshAlignMulBounds {
    /// `succ_mul_succ(m_ac0, k).0`.
    pub m_ac: ExprId,
    /// `succ_mul_succ(m_cb0, k).0`.
    pub m_cb: ExprId,
    /// `add (succ m_ac) m_cb`.
    pub combined: ExprId,
    /// `((deep_ab + deep_ac) + deep_cb) + big_n` — the common scale factor,
    /// exposed because [`CRealPrelude::riemann_sum_split_scale_invariant`]
    /// takes it as its own `k` argument.
    pub k: ExprId,
    /// `Nat.le deep_ab combined`.
    pub hle_ab: ExprId,
    /// `Nat.le deep_ac m_ac`.
    pub hle_ac: ExprId,
    /// `Nat.le deep_cb m_cb`.
    pub hle_cb: ExprId,
    /// `Nat.le big_n combined`.
    pub hn_ab: ExprId,
    /// `Nat.le big_n m_ac`.
    pub hn_ac: ExprId,
    /// `Nat.le big_n m_cb`.
    pub hn_cb: ExprId,
}

pub(super) fn mesh_count_align_mul_bounds(
    d: &mut IntDev<'_>,
    deep_ab: ExprId,
    deep_ac: ExprId,
    deep_cb: ExprId,
    m_ac0: ExprId,
    m_cb0: ExprId,
    big_n: ExprId,
) -> MeshAlignMulBounds {
    let np = d.prelude();

    // k := ((deep_ab + deep_ac) + deep_cb) + big_n.
    let t1 = NatOps::add(d, deep_ab, deep_ac);
    let t2 = NatOps::add(d, t1, deep_cb);
    let k = NatOps::add(d, t2, big_n);

    // The two scaled counts and the combined count.
    let (m_ac, _) = succ_mul_succ(d, m_ac0, k);
    let (m_cb, _) = succ_mul_succ(d, m_cb0, k);
    let succ_m_ac = d.succ(m_ac);
    let combined = NatOps::add(d, succ_m_ac, m_cb);

    // Shared tail of all three "modulus ≤ k" chains: `Le t2 k` and
    // `Le t1 t2`.
    let s_t2_k = d.lemma(np.le_add_right, &[t2, big_n]); // Le t2 k
    let s_t1_t2 = d.lemma(np.le_add_right, &[t1, deep_cb]); // Le t1 t2
    let s_t1_k = d.lemma(np.le_trans, &[t1, t2, k, s_t1_t2, s_t2_k]);

    // Le deep_ab k.
    let ab_t1 = d.lemma(np.le_add_right, &[deep_ab, deep_ac]);
    let h_ab_k = d.lemma(np.le_trans, &[deep_ab, t1, k, ab_t1, s_t1_k]);

    // Le deep_ac k.
    let ac_t1 = nat_le_add_left(d, deep_ab, deep_ac);
    let h_ac_k = d.lemma(np.le_trans, &[deep_ac, t1, k, ac_t1, s_t1_k]);

    // Le deep_cb k.
    let cb_t2 = nat_le_add_left(d, t1, deep_cb);
    let h_cb_k = d.lemma(np.le_trans, &[deep_cb, t2, k, cb_t2, s_t2_k]);

    // Le k m_ac and Le k m_cb -- the ONE inequality all three thresholds
    // reduce to. `succ_mul_succ(m0, k).0` is literally `add ((m0·k) + m0) k`,
    // so this is `nat_le_add_left` at that head.
    let ac_head = {
        let mk = NatOps::mul(d, m_ac0, k);
        d.const_app(np.add, &[mk, m_ac0])
    };
    let h_k_mac = nat_le_add_left(d, ac_head, k);
    let cb_head = {
        let mk = NatOps::mul(d, m_cb0, k);
        d.const_app(np.add, &[mk, m_cb0])
    };
    let h_k_mcb = nat_le_add_left(d, cb_head, k);

    // The three threshold facts.
    let hle_ac = d.lemma(np.le_trans, &[deep_ac, k, m_ac, h_ac_k, h_k_mac]);
    let hle_cb = d.lemma(np.le_trans, &[deep_cb, k, m_cb, h_cb_k, h_k_mcb]);
    let hle_ab = {
        let to_mac = d.lemma(np.le_trans, &[deep_ab, k, m_ac, h_ab_k, h_k_mac]);
        let mac_succ = d.lemma(np.le_succ, &[m_ac]);
        let to_succ = d.lemma(np.le_trans, &[deep_ab, m_ac, succ_m_ac, to_mac, mac_succ]);
        let succ_comb = d.lemma(np.le_add_right, &[succ_m_ac, m_cb]);
        d.lemma(
            np.le_trans,
            &[deep_ab, succ_m_ac, combined, to_succ, succ_comb],
        )
    };

    // `Nat.le big_n X` for each of the three counts. `big_n ≤ k` is
    // `nat_le_add_left` at `k`'s own head, and from there the three chains
    // reuse `h_k_mac`/`h_k_mcb` verbatim.
    let h_n_k = nat_le_add_left(d, t2, big_n);
    let hn_ac = d.lemma(np.le_trans, &[big_n, k, m_ac, h_n_k, h_k_mac]);
    let hn_cb = d.lemma(np.le_trans, &[big_n, k, m_cb, h_n_k, h_k_mcb]);
    let hn_ab = {
        let mac_succ = d.lemma(np.le_succ, &[m_ac]);
        let to_succ = d.lemma(np.le_trans, &[big_n, m_ac, succ_m_ac, hn_ac, mac_succ]);
        let succ_comb = d.lemma(np.le_add_right, &[succ_m_ac, m_cb]);
        d.lemma(
            np.le_trans,
            &[big_n, succ_m_ac, combined, to_succ, succ_comb],
        )
    };

    MeshAlignMulBounds {
        m_ac,
        m_cb,
        combined,
        k,
        hle_ab,
        hle_ac,
        hle_cb,
        hn_ab,
        hn_ac,
        hn_cb,
    }
}

#[cfg(test)]
mod mesh_count_align_mul_tests {
    use super::*;
    use crate::Declaration;

    /// Rebuild [`mesh_count_align_mul`]'s own `k`/`m_ac`/`m_cb`/`combined`
    /// independently, so a defect in ITS construction — not merely a matching
    /// bug in a test — is what the kernel's type-check catches.
    fn counts(
        d: &mut IntDev<'_>,
        deep_ab: ExprId,
        deep_ac: ExprId,
        deep_cb: ExprId,
        m_ac0: ExprId,
        m_cb0: ExprId,
        big_n: ExprId,
    ) -> (ExprId, ExprId, ExprId) {
        let t1 = NatOps::add(d, deep_ab, deep_ac);
        let t2 = NatOps::add(d, t1, deep_cb);
        let k = NatOps::add(d, t2, big_n);
        let (m_ac, _) = succ_mul_succ(d, m_ac0, k);
        let (m_cb, _) = succ_mul_succ(d, m_cb0, k);
        let succ_m_ac = d.succ(m_ac);
        let combined = NatOps::add(d, succ_m_ac, m_cb);
        (m_ac, m_cb, combined)
    }

    /// The `[a, b]` leg's existence claim (`∃ depth_ab, deep_ab + depth_ab =
    /// combined`), symbolic in all six inputs, closed into a real `Theorem`
    /// universally quantified over them — the same wrapping
    /// [`mesh_count_align_tests`]'s own positive control uses, and for the
    /// same reason (`Kernel::infer` on the unwrapped proof rejects the six as
    /// `UnboundFVar`). Confirms the proof is accepted by
    /// `Kernel::add_declaration`, not merely by `cargo check`.
    #[test]
    fn mesh_count_align_mul_proves_the_combined_threshold() {
        crate::on_a_deep_stack(mesh_count_align_mul_proves_the_combined_threshold_body);
    }

    fn mesh_count_align_mul_proves_the_combined_threshold_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();

        let fvs: Vec<_> = (0..6).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|fv| d.kernel().fvar(*fv)).collect();
        let (deep_ab, deep_ac, deep_cb, m_ac0, m_cb0, big_n) =
            (vars[0], vars[1], vars[2], vars[3], vars[4], vars[5]);

        let (exp_m_ac, exp_m_cb, combined) =
            counts(&mut d, deep_ab, deep_ac, deep_cb, m_ac0, m_cb0, big_n);

        let pred = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sum = NatOps::add(&mut d, deep_ab, j);
            let body = d.eq(sum, combined);
            d.lam_fv(j_fv, nat, body)
        };
        let target = exists_ty(&mut d, p, nat, pred);
        // The struct's REPORTED counts must be the same terms the proof is
        // about; a helper that proved the threshold for one `combined` while
        // handing the caller a different one would pass the kernel check and
        // still be unusable, so this is asserted rather than assumed.
        let build = |d: &mut IntDev<'_>, m: MeshAlignMul| -> ExprId {
            assert_eq!(m.m_ac, exp_m_ac, "reported m_ac must be the scaled count");
            assert_eq!(m.m_cb, exp_m_cb, "reported m_cb must be the scaled count");
            assert_eq!(
                m.combined, combined,
                "reported combined must be `add (succ m_ac) m_cb`"
            );
            exists_intro(d, p, nat, pred, m.depth_ab, m.eq_ab)
        };

        let proof = mesh_count_align_mul(
            &mut d, deep_ab, deep_ac, deep_cb, m_ac0, m_cb0, big_n, target, &build,
        );

        let mut ty = target;
        let mut value = proof;
        for fv in fvs.iter().rev() {
            ty = d.pi_fv(*fv, nat, ty);
            value = d.lam_fv(*fv, nat, value);
        }

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "meshCountAlignMulCombinedThresholdSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "mesh_count_align_mul must prove the [a,b] threshold, closed over all six inputs: {:?}",
            result.err()
        );
    }

    /// The two CHILD legs' existence claims (`∃ depth_ac, deep_ac + depth_ac =
    /// m_ac` and its `cb` mirror), which [`mesh_count_align`] never had to
    /// prove — it obtained them syntactically by *defining* `m_ac := deep_ac +
    /// depth_ac`, which is exactly what pins its split ratio at the midpoint.
    /// A version of [`mesh_count_align_mul`] whose `hle_ac`/`hle_cb` chains
    /// were wrong would still pass the combined-threshold test above, so this
    /// is a genuinely separate assertion, not a restatement.
    #[test]
    fn mesh_count_align_mul_proves_both_child_thresholds() {
        crate::on_a_deep_stack(mesh_count_align_mul_proves_both_child_thresholds_body);
    }

    fn mesh_count_align_mul_proves_both_child_thresholds_body() {
        for leg in ["ac", "cb"] {
            let mut kernel = crate::Kernel::new();
            let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
            let mut d = IntDev::new(&mut kernel, p.rat.int);
            let nat = d.nat_ty();

            let fvs: Vec<_> = (0..6).map(|_| d.fresh_fvar()).collect();
            let vars: Vec<ExprId> = fvs.iter().map(|fv| d.kernel().fvar(*fv)).collect();
            let (deep_ab, deep_ac, deep_cb, m_ac0, m_cb0, big_n) =
                (vars[0], vars[1], vars[2], vars[3], vars[4], vars[5]);

            let (m_ac, m_cb, _) = counts(&mut d, deep_ab, deep_ac, deep_cb, m_ac0, m_cb0, big_n);
            let (base, total) = if leg == "ac" {
                (deep_ac, m_ac)
            } else {
                (deep_cb, m_cb)
            };

            let pred = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let sum = NatOps::add(&mut d, base, j);
                let body = d.eq(sum, total);
                d.lam_fv(j_fv, nat, body)
            };
            let target = exists_ty(&mut d, p, nat, pred);
            let build = |d: &mut IntDev<'_>, m: MeshAlignMul| -> ExprId {
                let (depth, eq) = if leg == "ac" {
                    (m.depth_ac, m.eq_ac)
                } else {
                    (m.depth_cb, m.eq_cb)
                };
                exists_intro(d, p, nat, pred, depth, eq)
            };

            let proof = mesh_count_align_mul(
                &mut d, deep_ab, deep_ac, deep_cb, m_ac0, m_cb0, big_n, target, &build,
            );

            let mut ty = target;
            let mut value = proof;
            for fv in fvs.iter().rev() {
                ty = d.pi_fv(*fv, nat, ty);
                value = d.lam_fv(*fv, nat, value);
            }

            let anon = d.kernel().anon();
            let name = d
                .kernel()
                .name_str(anon, "meshCountAlignMulChildThresholdSmoke");
            let result = d.kernel().add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            });
            assert!(
                result.is_ok(),
                "mesh_count_align_mul must prove the [{leg}] child threshold: {:?}",
                result.err()
            );
        }
    }

    /// **The property [`mesh_count_align`] does not have**: the split fraction
    /// `succ(m_ac) / (combined + 1)` equals the caller's base fraction
    /// `succ(m_ac0) / (succ(m_ac0) + succ(m_cb0))` at every scale.
    ///
    /// Checked by `Kernel::def_eq` on concrete `Nat` literals rather than by
    /// rendering: `Nat.add`/`Nat.mul` do not reduce in `render_lean`, and a
    /// textual comparison reported a false mismatch for
    /// [`mesh_count_align`]'s own concrete test before that was noticed.
    /// Cross-multiplied to stay inside `Nat` (no rationals in the kernel's
    /// `Nat`): `succ(m_ac) · (succ(m_ac0) + succ(m_cb0)) = succ(m_ac0) ·
    /// (combined + 1)`.
    #[test]
    fn mesh_count_align_mul_preserves_the_base_ratio_at_every_scale() {
        crate::on_a_deep_stack(mesh_count_align_mul_preserves_the_base_ratio_at_every_scale_body);
    }

    fn mesh_count_align_mul_preserves_the_base_ratio_at_every_scale_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        // (m_ac0, m_cb0) = (0, 3) is a 1:5 split (c at 20% of [a,b]) -- the
        // FIFTEENTH lane's own worked example, the one the additive scheme
        // drives to 50%.
        for (m_ac0_v, m_cb0_v) in [(0u32, 3u32), (2, 5), (4, 1), (9, 90)] {
            for big_n_v in [0u32, 1, 4, 17] {
                let deep_ab = d.num(3);
                let deep_ac = d.num(5);
                let deep_cb = d.num(7);
                let m_ac0 = d.num(m_ac0_v);
                let m_cb0 = d.num(m_cb0_v);
                let big_n = d.num(big_n_v);

                let (m_ac, _m_cb, combined) =
                    counts(&mut d, deep_ab, deep_ac, deep_cb, m_ac0, m_cb0, big_n);
                let succ_m_ac = d.succ(m_ac);
                let combined_plus = d.succ(combined);
                let n_ac0 = d.succ(m_ac0);
                let n_cb0 = d.succ(m_cb0);
                let base_denom = NatOps::add(&mut d, n_ac0, n_cb0);

                let lhs = NatOps::mul(&mut d, succ_m_ac, base_denom);
                let rhs = NatOps::mul(&mut d, n_ac0, combined_plus);
                assert!(
                    d.kernel().def_eq(lhs, rhs),
                    "ratio must be preserved at (m_ac0={m_ac0_v}, m_cb0={m_cb0_v}, big_n={big_n_v}): \
                     succ(m_ac)*(n_ac0+n_cb0) = {} vs n_ac0*(combined+1) = {}",
                    d.kernel().render_lean(lhs),
                    d.kernel().render_lean(rhs)
                );
            }
        }
    }

    /// Negative control for the test above: [`mesh_count_align`]'s ADDITIVE
    /// counts FAIL that same cross-multiplied identity for a non-1:1 base
    /// ratio, so the assertion is discriminating rather than an arithmetic
    /// tautology that any pair of counts would satisfy.
    #[test]
    fn additive_mesh_count_align_does_not_preserve_the_base_ratio() {
        crate::on_a_deep_stack(additive_mesh_count_align_does_not_preserve_the_base_ratio_body);
    }

    fn additive_mesh_count_align_does_not_preserve_the_base_ratio_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        // The additive scheme's counts, exactly as `mesh_count_align` builds
        // them, at the same intended 1:5 base ratio (m_ac0=0, m_cb0=3).
        let deep_ab = d.num(3);
        let deep_ac = d.num(5);
        let deep_cb = d.num(7);
        let big_n = d.num(17);
        let m_ac0 = d.num(0);
        let m_cb0 = d.num(3);

        let depth = NatOps::add(&mut d, deep_ab, big_n);
        let m_ac = NatOps::add(&mut d, deep_ac, depth);
        let m_cb = NatOps::add(&mut d, deep_cb, depth);
        let succ_m_ac = d.succ(m_ac);
        let combined = NatOps::add(&mut d, succ_m_ac, m_cb);
        let combined_plus = d.succ(combined);
        let n_ac0 = d.succ(m_ac0);
        let n_cb0 = d.succ(m_cb0);
        let base_denom = NatOps::add(&mut d, n_ac0, n_cb0);

        let lhs = NatOps::mul(&mut d, succ_m_ac, base_denom);
        let rhs = NatOps::mul(&mut d, n_ac0, combined_plus);
        assert!(
            !d.kernel().def_eq(lhs, rhs),
            "the ADDITIVE scheme must NOT preserve a 1:5 base ratio -- if it does, \
             the positive ratio test above proves nothing"
        );
    }
}

// --- Gap B: riemannSum congruence in BOTH endpoints under `Equiv` ---------
//
// The SIXTEENTH `integral_split` entry's Gap B analysis: the combine does NOT
// need an `integral`-level endpoint congruence. It needs this one, at the
// `riemannSum` level, which the FIFTEENTH lane ruled out "even in principle"
// on the grounds that `sample x n` is rational while `Equiv` reals agree only
// in the limit. That argument is about proving the congruence SAMPLE BY
// SAMPLE; the route below never touches `sample`, and is assembled entirely
// out of machinery `declare_riemann_sum_split_exact_of_uc` already uses.

/// `Equiv (riemannSum F x y m) (riemannSum F x2 y2 m)` from `Equiv x x2` and
/// `Equiv y y2`, with `F` uniformly continuous on a common outer interval
/// `[aa, bb]` containing both sub-intervals.
///
/// **Why this is the lemma `integral_split` actually needs.** The combine's
/// three legs are `riemann_sum_integral_close` on `[a,b]`, `[a,c]`, `[c,b]`
/// at the CALLER's fixed `c`, glued by
/// [`CRealPrelude::riemann_sum_split_exact_of_uc`] — whose own split point is
/// `c_k := a + ofNat(succ m_ac) · delta_of(a, b, combined)`, a fresh `Nat`
/// arithmetic expression at every outer accuracy and therefore never
/// definitionally the caller's `c`. What has to be bridged is
/// `riemannSum F a c_k m_ac` against `riemannSum F a c m_ac` —
/// a `riemannSum`, not an `integral`. `Equiv c_k c` is exactly what
/// [`CRealPrelude::riemann_sum_split_scale_invariant`] already proves, once
/// the mesh family is [`mesh_count_align_mul`]'s multiplicative one.
///
/// **Route** (nothing new; every step names an existing lemma):
///
/// 1. `Equiv delta1 delta2` — [`CRealPrelude::neg_congr`] on the left
///    endpoints, [`CRealPrelude::add_congr`] into the width, then
///    [`CRealPrelude::mul_congr`] against a reflexive `1/(m+1)`.
/// 2. Per index `i < succ m`, `Equiv (samplePt1 i) (samplePt2 i)` — the same
///    two congruences again.
/// 3. Both sample points land in `[aa, bb]`:
///    [`CRealPrelude::riemann_sample_in_bounds`] places each inside its OWN
///    sub-interval, and two [`CRealPrelude::le_trans`] steps carry that out
///    to `[aa, bb]`.
/// 4. `Equiv (F samplePt1) (F samplePt2)` —
///    [`CRealPrelude::congr_of_uniformly_continuous`], which exists precisely
///    because a GLOBAL congruence hypothesis is unavailable for an `F`
///    continuous only on `[aa, bb]`.
/// 5. `mul_congr` on the summand, and [`sum_range_congr_lt_proof`] — the
///    `Nat.lt`-BOUNDED sum congruence, not
///    [`CRealPrelude::sum_range_congr`], for the same reason
///    [`declare_riemann_sum_split_exact_of_uc`] uses the bounded one: step 3
///    only places a sample point in range for `i < succ m`.
///
/// The result is stated against `sumRange` of the two [`summand_fn`]s, which
/// is `riemannSum`'s own `Definition` body at the same hash-consed `ExprId`s,
/// so a caller may use it directly at the [`rsum`] type.
#[allow(clippy::too_many_arguments)]
fn riemann_sum_congr_endpoints(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    aa: ExprId,
    bb: ExprId,
    u: ExprId,
    x: ExprId,
    y: ExprId,
    x2: ExprId,
    y2: ExprId,
    m: ExprId,
    hxy: ExprId,
    hx2y2: ExprId,
    hax: ExprId,
    hyb: ExprId,
    hax2: ExprId,
    hy2b: ExprId,
    hex: ExprId,
    hey: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let logic = p.rat.int.logic;

    let frac = frac_of(d, p, m);
    let w1 = width_of(d, p, x, y);
    let w2 = width_of(d, p, x2, y2);
    let delta1 = delta_of(d, p, x, y, m);
    let delta2 = delta_of(d, p, x2, y2, m);

    // h_delta : Equiv delta1 delta2.
    let h_delta = {
        let neg_x = cneg(d, p, x);
        let neg_x2 = cneg(d, p, x2);
        let h_neg = d.lemma(p.neg_congr, &[x, x2, hex]);
        let h_w = d.lemma(p.add_congr, &[y, y2, neg_x, neg_x2, hey, h_neg]);
        let refl_frac = d.lemma(p.equiv_refl, &[frac]);
        d.lemma(p.mul_congr, &[w1, w2, frac, frac, h_w, refl_frac])
    };

    let n = d.succ(m);
    let f_summand = summand_fn(d, p, f, x, delta1);
    let g_summand = summand_fn(d, p, f, x2, delta2);

    let bounded_pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_ty = d.lt(i, n);
        let lt_fv = d.fresh_fvar();
        let lt = d.kernel().fvar(lt_fv);

        let sp1 = sample_point(d, p, x, delta1, i);
        let sp2 = sample_point(d, p, x2, delta2, i);

        // Both sample points inside `[aa, bb]`, via their OWN sub-interval.
        let and1 = d.const_app(p.riemann_sample_in_bounds, &[x, y, m, i, hxy, lt]);
        let x_le_sp1 = cle(d, p, x, sp1);
        let sp1_le_y = cle(d, p, sp1, y);
        let lo1 = d.const_app(logic.and_left, &[x_le_sp1, sp1_le_y, and1]);
        let hi1 = d.const_app(logic.and_right, &[x_le_sp1, sp1_le_y, and1]);
        let h_a_sp1 = d.lemma(p.le_trans, &[aa, x, sp1, hax, lo1]);
        let h_sp1_b = d.lemma(p.le_trans, &[sp1, y, bb, hi1, hyb]);

        let and2 = d.const_app(p.riemann_sample_in_bounds, &[x2, y2, m, i, hx2y2, lt]);
        let x2_le_sp2 = cle(d, p, x2, sp2);
        let sp2_le_y2 = cle(d, p, sp2, y2);
        let lo2 = d.const_app(logic.and_left, &[x2_le_sp2, sp2_le_y2, and2]);
        let hi2 = d.const_app(logic.and_right, &[x2_le_sp2, sp2_le_y2, and2]);
        let h_a_sp2 = d.lemma(p.le_trans, &[aa, x2, sp2, hax2, lo2]);
        let h_sp2_b = d.lemma(p.le_trans, &[sp2, y2, bb, hi2, hy2b]);

        // h_pt : Equiv sp1 sp2.
        let oi = d.const_app(p.of_nat, &[i]);
        let sh1 = cmul(d, p, oi, delta1);
        let sh2 = cmul(d, p, oi, delta2);
        let refl_oi = d.lemma(p.equiv_refl, &[oi]);
        let h_sh = d.lemma(p.mul_congr, &[oi, oi, delta1, delta2, refl_oi, h_delta]);
        let h_pt = d.lemma(p.add_congr, &[x, x2, sh1, sh2, hex, h_sh]);

        // h_f : Equiv (F sp1) (F sp2) -- the BOUNDED congruence, since `F` is
        // uniformly continuous only on `[aa, bb]` and a global one does not
        // exist for such an `F` (that is `congr_of_uniformly_continuous`'s
        // whole reason for existing).
        let h_f = d.lemma(
            p.congr_of_uniformly_continuous,
            &[
                f, aa, bb, u, sp1, sp2, h_a_sp1, h_sp1_b, h_a_sp2, h_sp2_b, h_pt,
            ],
        );

        let fz1 = d.apply(f, &[sp1]);
        let fz2 = d.apply(f, &[sp2]);
        let h_summand = d.lemma(p.mul_congr, &[fz1, fz2, delta1, delta2, h_f, h_delta]);

        let with_lt = d.lam_fv(lt_fv, lt_ty, h_summand);
        d.lam_fv(i_fv, nat, with_lt)
    };

    let congr = sum_range_congr_lt_proof(d, p, f_summand, g_summand, n);
    d.apply(congr, &[bounded_pointwise])
}

#[cfg(test)]
mod riemann_sum_congr_endpoints_tests {
    use super::*;
    use crate::Declaration;

    /// Symbolic in `F`, both interval pairs, the outer interval, the witness
    /// and the mesh count, closed into a real `Theorem` — so the claim is
    /// checked by `Kernel::add_declaration`, not by `cargo check`, and against
    /// genuinely free variables rather than literals (numerals reduce, and
    /// reduction hides every defeq-shaped gap).
    ///
    /// The stated conclusion is written at the [`rsum`] type
    /// (`Equiv (riemannSum F x y m) (riemannSum F x2 y2 m)`), NOT at the
    /// `sumRange` type the proof term builds, so the test also pins that the
    /// two are the same `Definition` body at the same hash-consed `ExprId`s.
    #[test]
    fn riemann_sum_congr_endpoints_proves_the_stated_equiv() {
        crate::on_a_deep_stack(riemann_sum_congr_endpoints_proves_the_stated_equiv_body);
    }

    fn riemann_sum_congr_endpoints_proves_the_stated_equiv_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);
        let nat = d.nat_ty();
        let f_ty = fn_ty(&mut d, p);

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let aa_fv = d.fresh_fvar();
        let aa = d.kernel().fvar(aa_fv);
        let bb_fv = d.fresh_fvar();
        let bb = d.kernel().fvar(bb_fv);
        let u_ty = d.const_app(p.uniformly_continuous_on, &[f, aa, bb]);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);

        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let x2_fv = d.fresh_fvar();
        let x2 = d.kernel().fvar(x2_fv);
        let y2_fv = d.fresh_fvar();
        let y2 = d.kernel().fvar(y2_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);

        let hxy_ty = cle(&mut d, p, x, y);
        let hxy_fv = d.fresh_fvar();
        let hxy = d.kernel().fvar(hxy_fv);
        let hx2y2_ty = cle(&mut d, p, x2, y2);
        let hx2y2_fv = d.fresh_fvar();
        let hx2y2 = d.kernel().fvar(hx2y2_fv);
        let hax_ty = cle(&mut d, p, aa, x);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hyb_ty = cle(&mut d, p, y, bb);
        let hyb_fv = d.fresh_fvar();
        let hyb = d.kernel().fvar(hyb_fv);
        let hax2_ty = cle(&mut d, p, aa, x2);
        let hax2_fv = d.fresh_fvar();
        let hax2 = d.kernel().fvar(hax2_fv);
        let hy2b_ty = cle(&mut d, p, y2, bb);
        let hy2b_fv = d.fresh_fvar();
        let hy2b = d.kernel().fvar(hy2b_fv);
        let hex_ty = equiv(&mut d, p, x, x2);
        let hex_fv = d.fresh_fvar();
        let hex = d.kernel().fvar(hex_fv);
        let hey_ty = equiv(&mut d, p, y, y2);
        let hey_fv = d.fresh_fvar();
        let hey = d.kernel().fvar(hey_fv);

        let proof = riemann_sum_congr_endpoints(
            &mut d, p, f, aa, bb, u, x, y, x2, y2, m, hxy, hx2y2, hax, hyb, hax2, hy2b, hex, hey,
        );

        let lhs = rsum(&mut d, p, f, x, y, m);
        let rhs = rsum(&mut d, p, f, x2, y2, m);
        // Non-vacuity: the two sides must be genuinely different terms. A
        // conclusion that had collapsed to `Equiv X X` would be discharged by
        // `equiv_refl` and would prove nothing about endpoint congruence,
        // while still passing `add_declaration` below.
        assert_ne!(
            lhs, rhs,
            "the two riemannSums must be distinct terms, or the theorem is `Equiv X X`"
        );
        let concl = equiv(&mut d, p, lhs, rhs);

        let ty = {
            let t = d.arrow(hey_ty, concl);
            let t = d.arrow(hex_ty, t);
            let t = d.arrow(hy2b_ty, t);
            let t = d.arrow(hax2_ty, t);
            let t = d.arrow(hyb_ty, t);
            let t = d.arrow(hax_ty, t);
            let t = d.arrow(hx2y2_ty, t);
            let t = d.arrow(hxy_ty, t);
            let t = d.pi_fv(m_fv, nat, t);
            let t = d.pi_fv(y2_fv, carrier, t);
            let t = d.pi_fv(x2_fv, carrier, t);
            let t = d.pi_fv(y_fv, carrier, t);
            let t = d.pi_fv(x_fv, carrier, t);
            let t = d.arrow(u_ty, t);
            let t = d.pi_fv(bb_fv, carrier, t);
            let t = d.pi_fv(aa_fv, carrier, t);
            d.pi_fv(f_fv, f_ty, t)
        };
        let value = {
            let v = d.lam_fv(hey_fv, hey_ty, proof);
            let v = d.lam_fv(hex_fv, hex_ty, v);
            let v = d.lam_fv(hy2b_fv, hy2b_ty, v);
            let v = d.lam_fv(hax2_fv, hax2_ty, v);
            let v = d.lam_fv(hyb_fv, hyb_ty, v);
            let v = d.lam_fv(hax_fv, hax_ty, v);
            let v = d.lam_fv(hx2y2_fv, hx2y2_ty, v);
            let v = d.lam_fv(hxy_fv, hxy_ty, v);
            let v = d.lam_fv(m_fv, nat, v);
            let v = d.lam_fv(y2_fv, carrier, v);
            let v = d.lam_fv(x2_fv, carrier, v);
            let v = d.lam_fv(y_fv, carrier, v);
            let v = d.lam_fv(x_fv, carrier, v);
            let v = d.lam_fv(u_fv, u_ty, v);
            let v = d.lam_fv(bb_fv, carrier, v);
            let v = d.lam_fv(aa_fv, carrier, v);
            d.lam_fv(f_fv, f_ty, v)
        };

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "riemannSumCongrEndpointsSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "riemann_sum_congr_endpoints must prove the stated Equiv at the riemannSum type: {:?}",
            result.err()
        );
    }
}

/// `Equiv (riemannSum F a b combined) (add (riemannSum F a c m_ac)
/// (riemannSum F c b m_cb))` — [`CRealPrelude::riemann_sum_split_exact_of_uc`]'s
/// exact identity RESTATED AT THE CALLER'S OWN `c`, given only that `c` is
/// `Equiv` to that theorem's internally-computed split point `c_k`.
///
/// This is the join between the SIXTEENTH `integral_split` entry's two gap
/// resolutions, and it is the shape `integral_split`'s combine needs: the
/// three `riemann_sum_integral_close` legs are stated at the caller's fixed
/// `c` (they must be — the caller supplies `hac`/`uac`/`hcb`/`ucb` once),
/// while `riemann_sum_split_exact_of_uc` can only speak about `c_k := a +
/// ofNat(succ m_ac) · delta_of(a, b, combined)`, a fresh `Nat` arithmetic
/// expression at every accuracy.
///
/// `Equiv c_k c` is exactly what
/// [`CRealPrelude::riemann_sum_split_scale_invariant`] proves, and only for
/// the [`succ_mul_succ`] family — which is why [`mesh_count_align_mul`] is a
/// PREREQUISITE for this and [`mesh_count_align`]'s additive padding is not
/// merely a worse choice but an unusable one (there is no `c_0` to be `Equiv`
/// to).
///
/// Two [`riemann_sum_congr_endpoints`] applications, one per summand — the
/// first moving the RIGHT endpoint (`[a, c_k] → [a, c]`), the second the LEFT
/// (`[c_k, b] → [c, b]`), which is why that helper varies both — combined by
/// [`CRealPrelude::add_congr`] and chained onto the split identity.
#[allow(clippy::too_many_arguments)]
fn split_identity_at_equiv_point(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    u: ExprId,
    hab: ExprId,
    m_ac: ExprId,
    m_cb: ExprId,
    c: ExprId,
    hac_k: ExprId,
    hc_kb: ExprId,
    hac: ExprId,
    hcb: ExprId,
    hc: ExprId,
) -> ExprId {
    // `c_k` and `combined`, rebuilt exactly as
    // `declare_riemann_sum_split_exact` builds them, so interning makes these
    // the SAME `ExprId`s the theorem's own conclusion mentions.
    let n_ac = d.succ(m_ac);
    let combined = NatOps::add(d, n_ac, m_cb);
    let delta_ab = delta_of(d, p, a, b, combined);
    let on_ac = d.const_app(p.of_nat, &[n_ac]);
    let w1 = cmul(d, p, on_ac, delta_ab);
    let c_k = cadd(d, p, a, w1);

    let split = d.lemma(
        p.riemann_sum_split_exact_of_uc,
        &[f, a, b, m_ac, m_cb, u, hab],
    );

    let refl_a_le = d.lemma(p.le_refl, &[a]);
    let refl_b_le = d.lemma(p.le_refl, &[b]);
    let refl_a_eq = d.lemma(p.equiv_refl, &[a]);
    let refl_b_eq = d.lemma(p.equiv_refl, &[b]);

    // leg1 : Equiv (riemannSum F a c_k m_ac) (riemannSum F a c m_ac).
    let leg1 = riemann_sum_congr_endpoints(
        d, p, f, a, b, u, a, c_k, a, c, m_ac, hac_k, hac, refl_a_le, hc_kb, refl_a_le, hcb,
        refl_a_eq, hc,
    );
    // leg2 : Equiv (riemannSum F c_k b m_cb) (riemannSum F c b m_cb).
    // NOTE the outer interval is `(a, b)` in BOTH legs, never `(c_k, b)`:
    // `u` witnesses uniform continuity on `[a, b]` and on nothing else. A
    // first version passed `(c_k, b)` here -- reading the leg's own
    // sub-interval as the witness's interval -- and the kernel rejected it
    // with a bare `TypeMismatch` naming neither `u` nor `c_k`.
    let leg2 = riemann_sum_congr_endpoints(
        d, p, f, a, b, u, c_k, b, c, b, m_cb, hc_kb, hcb, hac_k, refl_b_le, hac, refl_b_le, hc,
        refl_b_eq,
    );

    let l1 = rsum(d, p, f, a, c_k, m_ac);
    let l2 = rsum(d, p, f, c_k, b, m_cb);
    let r1 = rsum(d, p, f, a, c, m_ac);
    let r2 = rsum(d, p, f, c, b, m_cb);
    let mid = cadd(d, p, l1, l2);
    let rhs = cadd(d, p, r1, r2);
    let combine = d.lemma(p.add_congr, &[l1, r1, l2, r2, leg1, leg2]);

    let lhs = rsum(d, p, f, a, b, combined);
    echain(d, p, lhs, &[(mid, split), (rhs, combine)])
}

#[cfg(test)]
mod split_identity_at_equiv_point_tests {
    use super::*;
    use crate::Declaration;

    /// Symbolic in every input, closed into a real `Theorem`. This is the
    /// first thing in this file to CONSUME both of the SIXTEENTH lane's gap
    /// resolutions at once, so it is also the check that they compose: a
    /// [`riemann_sum_congr_endpoints`] whose endpoint roles were transposed
    /// would still prove its own smoke test and fail here.
    #[test]
    fn split_identity_at_equiv_point_proves_the_stated_identity() {
        crate::on_a_deep_stack(split_identity_at_equiv_point_proves_the_stated_identity_body);
    }

    fn split_identity_at_equiv_point_proves_the_stated_identity_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);
        let nat = d.nat_ty();
        let f_ty = fn_ty(&mut d, p);

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let hab_ty = cle(&mut d, p, a, b);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);

        let mac_fv = d.fresh_fvar();
        let m_ac = d.kernel().fvar(mac_fv);
        let mcb_fv = d.fresh_fvar();
        let m_cb = d.kernel().fvar(mcb_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);

        // Rebuild `c_k` independently, mirroring the helper's own
        // construction, so a defect in ITS reconstruction is what the kernel
        // catches rather than a matching bug here.
        let n_ac = d.succ(m_ac);
        let combined = NatOps::add(&mut d, n_ac, m_cb);
        let delta_ab = delta_of(&mut d, p, a, b, combined);
        let on_ac = d.const_app(p.of_nat, &[n_ac]);
        let w1 = cmul(&mut d, p, on_ac, delta_ab);
        let c_k = cadd(&mut d, p, a, w1);

        let hac_k_ty = cle(&mut d, p, a, c_k);
        let hac_k_fv = d.fresh_fvar();
        let hac_k = d.kernel().fvar(hac_k_fv);
        let hc_kb_ty = cle(&mut d, p, c_k, b);
        let hc_kb_fv = d.fresh_fvar();
        let hc_kb = d.kernel().fvar(hc_kb_fv);
        let hac_ty = cle(&mut d, p, a, c);
        let hac_fv = d.fresh_fvar();
        let hac = d.kernel().fvar(hac_fv);
        let hcb_ty = cle(&mut d, p, c, b);
        let hcb_fv = d.fresh_fvar();
        let hcb = d.kernel().fvar(hcb_fv);
        let hc_ty = equiv(&mut d, p, c_k, c);
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);

        let proof = split_identity_at_equiv_point(
            &mut d, p, f, a, b, u, hab, m_ac, m_cb, c, hac_k, hc_kb, hac, hcb, hc,
        );

        let lhs = rsum(&mut d, p, f, a, b, combined);
        let r1 = rsum(&mut d, p, f, a, c, m_ac);
        let r2 = rsum(&mut d, p, f, c, b, m_cb);
        let rhs = cadd(&mut d, p, r1, r2);
        // Non-vacuity: the conclusion must mention the CALLER's `c`, not the
        // internally-computed `c_k`. If it collapsed to the latter this would
        // just be `riemann_sum_split_exact_of_uc` restated, and the two
        // congruence legs would be doing nothing.
        let l1 = rsum(&mut d, p, f, a, c_k, m_ac);
        assert_ne!(
            r1, l1,
            "the conclusion must be about the caller's `c`, not the computed `c_k`"
        );
        let concl = equiv(&mut d, p, lhs, rhs);

        let ty = {
            let t = d.arrow(hc_ty, concl);
            let t = d.arrow(hcb_ty, t);
            let t = d.arrow(hac_ty, t);
            let t = d.arrow(hc_kb_ty, t);
            let t = d.arrow(hac_k_ty, t);
            let t = d.pi_fv(c_fv, carrier, t);
            let t = d.pi_fv(mcb_fv, nat, t);
            let t = d.pi_fv(mac_fv, nat, t);
            let t = d.arrow(hab_ty, t);
            let t = d.arrow(u_ty, t);
            let t = d.pi_fv(b_fv, carrier, t);
            let t = d.pi_fv(a_fv, carrier, t);
            d.pi_fv(f_fv, f_ty, t)
        };
        let value = {
            let v = d.lam_fv(hc_fv, hc_ty, proof);
            let v = d.lam_fv(hcb_fv, hcb_ty, v);
            let v = d.lam_fv(hac_fv, hac_ty, v);
            let v = d.lam_fv(hc_kb_fv, hc_kb_ty, v);
            let v = d.lam_fv(hac_k_fv, hac_k_ty, v);
            let v = d.lam_fv(c_fv, carrier, v);
            let v = d.lam_fv(mcb_fv, nat, v);
            let v = d.lam_fv(mac_fv, nat, v);
            let v = d.lam_fv(hab_fv, hab_ty, v);
            let v = d.lam_fv(u_fv, u_ty, v);
            let v = d.lam_fv(b_fv, carrier, v);
            let v = d.lam_fv(a_fv, carrier, v);
            d.lam_fv(f_fv, f_ty, v)
        };

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "splitIdentityAtEquivPointSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "split_identity_at_equiv_point must prove the identity at the caller's c: {:?}",
            result.err()
        );
    }
}

// --- the declarations ---------------------------------------------------------

/// `CReal.riemannSum (f : CReal -> CReal) (a b : CReal) (m : Nat) : CReal :=
///   CReal.sumRange (fun i => mul (f (add a (mul (ofNat i) delta))) delta)
///     (Nat.succ m)`, where `delta = mul (add b (neg a)) (ofRat (natDivSucc 1 m))`.
fn declare_riemann_sum(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let delta = delta_of(d, p, a, b, m);
    let n = d.succ(m);
    let summand = summand_fn(d, p, f, a, delta);
    let body = d.const_app(p.sum_range, &[summand, n]);

    let value = {
        let with_m = d.lam_fv(m_fv, nat, body);
        let with_b = d.lam_fv(b_fv, carrier, with_m);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(f_fv, f_ty, with_a)
    };
    let ty = {
        let over_m = d.arrow(nat, carrier);
        let over_b = d.arrow(carrier, over_m);
        let over_a = d.arrow(carrier, over_b);
        d.arrow(f_ty, over_a)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.riemann_sum,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(RIEMANN_HEIGHT),
    })
}

/// `CReal.riemannSum_add : ∀ f g a b m,
/// Equiv (riemannSum (fun r => add (f r) (g r)) a b m)
///       (add (riemannSum f a b m) (riemannSum g a b m))`.
///
/// Route: `sum_range_congr` against [`right_distrib`] turns the combined
/// summand `(f(x)+g(x))·Δ` into `f(x)·Δ + g(x)·Δ` pointwise, then
/// `sum_range_add` splits the sum.
fn declare_riemann_sum_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let combined = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(g, &[r]);
        let body = cadd(d, p, fr, gr);
        d.lam_fv(r_fv, carrier, body)
    };

    let delta = delta_of(d, p, a, b, m);
    let n = d.succ(m);

    let f_summand_combined = summand_fn(d, p, combined, a, delta);
    let f_summand_plain = summand_fn(d, p, f, a, delta);
    let g_summand_plain = summand_fn(d, p, g, a, delta);

    // f_summand_split i := add (mul (f si) delta) (mul (g si) delta).
    let f_summand_split = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = sample_point(d, p, a, delta, i);
        let fx = d.apply(f, &[sp]);
        let gx = d.apply(g, &[sp]);
        let ft = cmul(d, p, fx, delta);
        let gt = cmul(d, p, gx, delta);
        let body = cadd(d, p, ft, gt);
        d.lam_fv(i_fv, nat, body)
    };

    // h1 : Equiv (sumRange f_summand_combined n) (sumRange f_summand_split n).
    let h1 = {
        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let sp = sample_point(d, p, a, delta, i);
            let fx = d.apply(f, &[sp]);
            let gx = d.apply(g, &[sp]);
            let step = right_distrib(d, p, fx, gx, delta);
            d.lam_fv(i_fv, nat, step)
        };
        d.lemma(
            p.sum_range_congr,
            &[f_summand_combined, f_summand_split, n, pointwise],
        )
    };

    // h2 : Equiv (sumRange f_summand_split n)
    //            (add (sumRange f_summand_plain n) (sumRange g_summand_plain n)).
    let h2 = d.lemma(p.sum_range_add, &[f_summand_plain, g_summand_plain, n]);

    let lhs = d.const_app(p.sum_range, &[f_summand_combined, n]);
    let mid = d.const_app(p.sum_range, &[f_summand_split, n]);
    let rhs = {
        let sf = d.const_app(p.sum_range, &[f_summand_plain, n]);
        let sg = d.const_app(p.sum_range, &[g_summand_plain, n]);
        cadd(d, p, sf, sg)
    };

    let proof = d.lemma(p.equiv_trans, &[lhs, mid, rhs, h1, h2]);

    let ty = {
        let lhs_rs = rsum(d, p, combined, a, b, m);
        let rf = rsum(d, p, f, a, b, m);
        let rg = rsum(d, p, g, a, b, m);
        let rhs_rs = cadd(d, p, rf, rg);
        equiv(d, p, lhs_rs, rhs_rs)
    };

    let ty_full = {
        let over_m = d.pi_fv(m_fv, nat, ty);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_g = d.pi_fv(g_fv, f_ty, over_a);
        d.pi_fv(f_fv, f_ty, over_g)
    };
    let value_full = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_g = d.lam_fv(g_fv, f_ty, over_a);
        d.lam_fv(f_fv, f_ty, over_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_add,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

/// `CReal.mul_riemannSum : ∀ c f a b m,
/// Equiv (riemannSum (fun r => mul c (f r)) a b m) (mul c (riemannSum f a b m))`.
///
/// Route: `sum_range_congr` against `mul_assoc` re-associates `(c·f(x))·Δ` to
/// `c·(f(x)·Δ)` pointwise, then `mul_sum_range` pulls `c` out of the sum.
fn declare_mul_riemann_sum(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let combined = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let body = cmul(d, p, c, fr);
        d.lam_fv(r_fv, carrier, body)
    };

    let delta = delta_of(d, p, a, b, m);
    let n = d.succ(m);

    let f_summand_combined = summand_fn(d, p, combined, a, delta);
    let f_summand_plain = summand_fn(d, p, f, a, delta);

    // w_summand i := mul c (f_summand_plain i) = mul c (mul (f si) delta).
    let w_summand = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = sample_point(d, p, a, delta, i);
        let fx = d.apply(f, &[sp]);
        let inner = cmul(d, p, fx, delta);
        let body = cmul(d, p, c, inner);
        d.lam_fv(i_fv, nat, body)
    };

    // h1 : Equiv (sumRange f_summand_combined n) (sumRange w_summand n),
    // pointwise via mul_assoc: (c*fx)*delta ~ c*(fx*delta).
    let h1 = {
        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let sp = sample_point(d, p, a, delta, i);
            let fx = d.apply(f, &[sp]);
            let step = d.lemma(p.mul_assoc, &[c, fx, delta]);
            d.lam_fv(i_fv, nat, step)
        };
        d.lemma(
            p.sum_range_congr,
            &[f_summand_combined, w_summand, n, pointwise],
        )
    };

    // h_ms : Equiv (mul c (sumRange f_summand_plain n)) (sumRange w_summand n).
    let h_ms = d.lemma(p.mul_sum_range, &[c, f_summand_plain, n]);

    let sum_plain = d.const_app(p.sum_range, &[f_summand_plain, n]);
    let mul_c_sum = cmul(d, p, c, sum_plain);
    let sum_w = d.const_app(p.sum_range, &[w_summand, n]);

    // h2 : Equiv (sumRange w_summand n) (mul c (sumRange f_summand_plain n)).
    let h2 = d.lemma(p.equiv_symm, &[mul_c_sum, sum_w, h_ms]);

    let lhs = d.const_app(p.sum_range, &[f_summand_combined, n]);
    let proof = d.lemma(p.equiv_trans, &[lhs, sum_w, mul_c_sum, h1, h2]);

    let ty = {
        let lhs_rs = rsum(d, p, combined, a, b, m);
        let rf = rsum(d, p, f, a, b, m);
        let rhs_rs = cmul(d, p, c, rf);
        equiv(d, p, lhs_rs, rhs_rs)
    };

    let ty_full = {
        let over_m = d.pi_fv(m_fv, nat, ty);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_f = d.pi_fv(f_fv, f_ty, over_a);
        d.pi_fv(c_fv, carrier, over_f)
    };
    let value_full = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_f = d.lam_fv(f_fv, f_ty, over_a);
        d.lam_fv(c_fv, carrier, over_f)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_riemann_sum,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

/// `delta := mul (width_of a b) (embed (natDivSucc 1 m))` together with a
/// proof `le zero delta`, given `hab : le a b`. Shared by
/// [`declare_riemann_sum_le`] and [`declare_riemann_sample_in_bounds`]: `le a
/// b` is what makes the width `b − a` nonneg (via `add_le_add` shifted by
/// `neg a`), and the mesh factor `1/(m+1)` is unconditionally nonneg, so
/// `mul_nonneg` closes it.
fn delta_nonneg_of(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    m: ExprId,
    hab: ExprId,
) -> (ExprId, ExprId) {
    let width = width_of(d, p, a, b);
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_real = embed(d, p, frac);
    let delta = cmul(d, p, width, frac_real);
    let zero_c = czero(d, p);

    // width_nonneg : le zero (add b (neg a)), from `le a b`.
    let width_nonneg = {
        let na = cneg(d, p, a);
        let refl_na = d.lemma(p.le_refl, &[na]);
        let a_na = cadd(d, p, a, na);
        let b_na = cadd(d, p, b, na);
        let shifted = d.lemma(p.add_le_add, &[a, b, na, na, hab, refl_na]);
        // shifted : le (add a (neg a)) (add b (neg a))
        let hn = d.lemma(p.add_neg, &[a]); // Equiv (add a (neg a)) zero
        let refl_bna = d.lemma(p.equiv_refl, &[b_na]);
        d.lemma(
            p.le_congr,
            &[a_na, zero_c, b_na, b_na, hn, refl_bna, shifted],
        )
    };

    // frac_nonneg : le zero (ofRat (natDivSucc 1 m)).
    let frac_nonneg = {
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, m]);
        d.lemma(p.of_rat_le, &[rzero, frac, rle])
    };

    // delta_nonneg : le zero delta.
    let delta_nonneg = d.lemma(p.mul_nonneg, &[width, frac_real, width_nonneg, frac_nonneg]);
    (delta, delta_nonneg)
}

/// `CReal.riemannSum_le : ∀ f g a b m, le a b → (∀ z, le (f z) (g z)) →
/// le (riemannSum f a b m) (riemannSum g a b m)`.
///
/// `le a b` is what makes `Δ ≥ 0` (via `mul_nonneg` on the width `b − a` and
/// the always-nonnegative rational mesh factor), which
/// `mul_le_mul_of_nonneg_left` needs to multiply the pointwise hypothesis
/// through by `Δ` without reversing it. See the module documentation for why
/// the pointwise hypothesis is global rather than restricted to `[a, b]`.
fn declare_riemann_sum_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let hfg_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let body = cle(d, p, fz, gz);
        d.pi_fv(z_fv, carrier, body)
    };
    let hfg_fv = d.fresh_fvar();
    let hfg = d.kernel().fvar(hfg_fv);

    let (delta, delta_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let n = d.succ(m);

    let f_summand = summand_fn(d, p, f, a, delta);
    let g_summand = summand_fn(d, p, g, a, delta);

    let bounded_pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = sample_point(d, p, a, delta, i);
        let fz = d.apply(f, &[sp]);
        let gz = d.apply(g, &[sp]);
        let h_fg = d.apply(hfg, &[sp]); // le (f sp) (g sp)

        let step = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[delta, fz, gz, delta_nonneg, h_fg],
        );
        // step : le (mul delta fz) (mul delta gz)
        let comm_f = d.lemma(p.mul_comm, &[delta, fz]); // Equiv (mul delta fz) (mul fz delta)
        let comm_g = d.lemma(p.mul_comm, &[delta, gz]);
        let df = cmul(d, p, delta, fz);
        let dg = cmul(d, p, delta, gz);
        let fd = cmul(d, p, fz, delta);
        let gd = cmul(d, p, gz, delta);
        let transported = d.lemma(p.le_congr, &[df, fd, dg, gd, comm_f, comm_g, step]);
        // transported : le (mul fz delta) (mul gz delta) = le (f_summand i) (g_summand i)

        let lt_hyp_ty = d.lt(i, n);
        let lt_fv = d.fresh_fvar();
        let with_lt = d.lam_fv(lt_fv, lt_hyp_ty, transported);
        d.lam_fv(i_fv, nat, with_lt)
    };

    let result = d.lemma(
        p.sum_range_le,
        &[f_summand, g_summand, n, bounded_pointwise],
    );

    let ty = {
        let lhs_rs = rsum(d, p, f, a, b, m);
        let rhs_rs = rsum(d, p, g, a, b, m);
        cle(d, p, lhs_rs, rhs_rs)
    };
    let ty_inner = {
        let after_hfg = d.arrow(hfg_ty, ty);
        d.arrow(hab_ty, after_hfg)
    };
    let ty_full = {
        let over_m = d.pi_fv(m_fv, nat, ty_inner);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_g = d.pi_fv(g_fv, f_ty, over_a);
        d.pi_fv(f_fv, f_ty, over_g)
    };
    let value_inner = {
        let with_hfg = d.lam_fv(hfg_fv, hfg_ty, result);
        d.lam_fv(hab_fv, hab_ty, with_hfg)
    };
    let value_full = {
        let over_m = d.lam_fv(m_fv, nat, value_inner);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_g = d.lam_fv(g_fv, f_ty, over_a);
        d.lam_fv(f_fv, f_ty, over_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_le,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

// --- sample points lie in `[a, b]` ------------------------------------------

/// `CReal.le zero (CReal.ofNat n)` — `CReal.ofNat` is nonneg. Directly from
/// `Rat.zero_le_natDivSucc` lifted across [`CRealPrelude::of_rat_le`] — the
/// same route [`delta_nonneg_of`]'s `frac_nonneg` uses for the mesh factor.
fn zero_le_of_nat(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let zero_nat = d.num(0);
    let rat_n = d.const_app(p.rat.nat_div_succ, &[n, zero_nat]);
    let rzero = d.kernel().const_(p.rat.zero, vec![]);
    let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[n, zero_nat]);
    d.lemma(p.of_rat_le, &[rzero, rat_n, rle])
    // : CReal.le (embed rzero) (embed rat_n) -- defeq CReal.le zero (ofNat n)
}

/// `CReal.le x (add x w)`, given `hw : CReal.le zero w` — for a general
/// nonneg ADDEND `w : CReal`. No public `CReal` prelude lemma gives this: only
/// [`CRealPrelude::le_add_of_nonneg`] does, and only for `w := embed q` at a
/// nonneg RATIONAL `q`. Built directly from `add_le_add`/`add_zero`/`le_congr`
/// — the same three steps `le_add_of_nonneg`'s own proof runs, generalized off
/// the rational embedding.
fn shift_le_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    w: ExprId,
    hw: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let refl_x = d.lemma(p.le_refl, &[x]);
    let grown = d.lemma(p.add_le_add, &[x, x, zero_c, w, refl_x, hw]);
    // grown : le (add x zero) (add x w)
    let padded = cadd(d, p, x, zero_c);
    let target = cadd(d, p, x, w);
    let trim = d.lemma(p.add_zero, &[x]); // Equiv (add x zero) x
    let refl_target = d.lemma(p.equiv_refl, &[target]);
    d.lemma(
        p.le_congr,
        &[padded, x, target, target, trim, refl_target, grown],
    )
    // : le x (add x w)
}

/// `Equiv (add a (add b (neg a))) b` — `a + (b − a) ~ b`, the ring identity
/// [`add_sub_cancel`]'s callers need to fold `a + width` back down to `b`.
fn add_sub_cancel(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na); // b + (-a)
    let start = cadd(d, p, a, width); // a + (b + (-a))

    let nab = cadd(d, p, na, b); // (-a) + b
    let s1 = cadd(d, p, a, nab); // a + ((-a) + b)
    let h1 = {
        let comm = d.lemma(p.add_comm, &[b, na]); // Equiv width nab
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        d.lemma(p.add_congr, &[a, a, width, nab, refl_a, comm])
        // : Equiv start s1
    };

    let ana = cadd(d, p, a, na); // a + (-a)
    let s2 = cadd(d, p, ana, b); // (a + (-a)) + b
    let h2 = {
        let assoc = d.lemma(p.add_assoc, &[a, na, b]);
        // assoc : Equiv (add (add a na) b) (add a (add na b)) = Equiv s2 s1
        d.lemma(p.equiv_symm, &[s2, s1, assoc]) // : Equiv s1 s2
    };

    let zero_c = czero(d, p);
    let s3 = cadd(d, p, zero_c, b); // zero + b
    let h3 = {
        let hn = d.lemma(p.add_neg, &[a]); // Equiv ana zero
        let refl_b = d.lemma(p.equiv_refl, &[b]);
        d.lemma(p.add_congr, &[ana, zero_c, b, b, hn, refl_b])
        // : Equiv s2 s3
    };

    let s4 = cadd(d, p, b, zero_c); // b + zero
    let h4 = d.lemma(p.add_comm, &[zero_c, b]); // Equiv s3 s4

    let h5 = d.lemma(p.add_zero, &[b]); // Equiv s4 b

    echain(
        d,
        p,
        start,
        &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (b, h5)],
    )
}

/// `Equiv (add x (neg (add x (neg y)))) y` — `x − (x − y) ~ y`, the mirror
/// cancellation [`declare_two_sided_of_abs_sub_le`]'s second (`neg_le_abs`)
/// branch needs. Derived from [`add_sub_cancel`]`(y, x) : Equiv (add y diff)
/// x` (`diff := add x (neg y)`) by adding `neg diff` to BOTH sides of that
/// equation and simplifying the left with `add_assoc`/`add_neg`/`add_zero` —
/// `diff` itself is never unfolded, so this needs no `neg`-distributes-over-
/// `add` law.
fn diff_cancel_left(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny); // x + (-y)
    let ndiff = cneg(d, p, diff);

    let cancel_yx = add_sub_cancel(d, p, y, x); // Equiv (add y diff) x
    let y_diff = cadd(d, p, y, diff);
    let start = cadd(d, p, y_diff, ndiff); // (y + diff) + (-diff)
    let target = cadd(d, p, x, ndiff); // x + (-diff)

    let h1 = {
        // Equiv start target, by congr-ing `cancel_yx` into the left slot.
        let refl_ndiff = d.lemma(p.equiv_refl, &[ndiff]);
        d.lemma(
            p.add_congr,
            &[y_diff, x, ndiff, ndiff, cancel_yx, refl_ndiff],
        )
    };

    let diff_ndiff = cadd(d, p, diff, ndiff); // diff + (-diff)
    let s1 = cadd(d, p, y, diff_ndiff); // y + (diff + (-diff))
    let h_assoc = d.lemma(p.add_assoc, &[y, diff, ndiff]); // Equiv start s1

    let zero_c = czero(d, p);
    let s2 = cadd(d, p, y, zero_c); // y + zero
    let h_s1_s2 = {
        let hn = d.lemma(p.add_neg, &[diff]); // Equiv (add diff ndiff) zero
        let refl_y = d.lemma(p.equiv_refl, &[y]);
        d.lemma(p.add_congr, &[y, y, diff_ndiff, zero_c, refl_y, hn])
    };

    let h_s2_y = d.lemma(p.add_zero, &[y]); // Equiv s2 y

    let start_eq_y = echain(d, p, start, &[(s1, h_assoc), (s2, h_s1_s2), (y, h_s2_y)]);
    // start_eq_y : Equiv start y

    let symm_h1 = d.lemma(p.equiv_symm, &[start, target, h1]); // Equiv target start

    echain(d, p, target, &[(start, symm_h1), (y, start_eq_y)])
    // : Equiv target y
}

/// `Equiv (mul (ofNat (Nat.succ m)) (mul width frac)) width`, where `frac :=
/// embed (Rat.natDivSucc 1 m)` — `n · Δ ~ (b − a)` when `Δ := width · frac`,
/// exactly (no error term), for every `m`. The width-only case of
/// [`riemann_sum_const_rearrange`]'s own algebra (that one additionally
/// carries a constant factor `c`), reusing [`mesh_inverse_identity`].
fn mesh_times_count_eq_width(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    width: ExprId,
    frac: ExprId,
    m: ExprId,
) -> ExprId {
    let on = {
        let successor = d.succ(m);
        d.const_app(p.of_nat, &[successor])
    };
    let delta = cmul(d, p, width, frac);
    let a_start = cmul(d, p, on, delta); // mul on (mul width frac)

    let on_width = cmul(d, p, on, width);
    let width_on = cmul(d, p, width, on);
    let on_frac = cmul(d, p, on, frac);

    // b1 := mul (mul on width) frac
    let b1 = cmul(d, p, on_width, frac);
    let h1 = {
        let assoc = d.lemma(p.mul_assoc, &[on, width, frac]); // Equiv b1 a_start
        d.lemma(p.equiv_symm, &[b1, a_start, assoc]) // Equiv a_start b1
    };

    // b2 := mul (mul width on) frac
    let b2 = cmul(d, p, width_on, frac);
    let h2 = {
        let comm = d.lemma(p.mul_comm, &[on, width]); // Equiv on_width width_on
        let refl_frac = d.lemma(p.equiv_refl, &[frac]);
        d.lemma(
            p.mul_congr,
            &[on_width, width_on, frac, frac, comm, refl_frac],
        )
        // Equiv b1 b2
    };

    // b3 := mul width (mul on frac)
    let b3 = cmul(d, p, width, on_frac);
    // assoc(width,on,frac) : Equiv (mul (mul width on) frac) (mul width (mul on frac)) = Equiv b2 b3
    let h3 = d.lemma(p.mul_assoc, &[width, on, frac]);

    // b4 := mul width one
    let one_c = d.kernel().const_(p.one, vec![]);
    let b4 = cmul(d, p, width, one_c);
    let h4 = {
        let cancel = mesh_inverse_identity(d, p, m); // Equiv on_frac one_c
        let refl_width = d.lemma(p.equiv_refl, &[width]);
        d.lemma(
            p.mul_congr,
            &[width, width, on_frac, one_c, refl_width, cancel],
        )
        // Equiv b3 b4
    };

    let h5 = d.lemma(p.mul_one, &[width]); // Equiv (mul width one) width = Equiv b4 width

    echain(
        d,
        p,
        a_start,
        &[(b1, h1), (b2, h2), (b3, h3), (b4, h4), (width, h5)],
    )
}

/// `Nat.le i n`, from `hlt : Nat.lt i n` (defeq `Nat.le (succ i) n`) — via
/// `Nat.le_succ i : Nat.le i (succ i)` and `Nat.le_trans`.
fn nat_le_of_lt(d: &mut IntDev<'_>, i: ExprId, n: ExprId, hlt: ExprId) -> ExprId {
    let np = d.prelude();
    let succ_i = d.succ(i);
    let step = d.const_app(np.le_succ, &[i]); // Nat.le i (succ i)
    d.const_app(np.le_trans, &[i, succ_i, n, step, hlt])
}

/// `CReal.riemannSum_sample_in_bounds : ∀ a b m i, le a b → Nat.lt i (Nat.succ
/// m) → And (le a (add a (mul (ofNat i) delta))) (le (add a (mul (ofNat i)
/// delta)) b)`, where `delta := (b − a) · ofRat (Rat.natDivSucc 1 m)` exactly
/// as in `riemannSum` itself — every LEFT-endpoint sample point of a Riemann
/// sum over `[a, b]` lies in `[a, b]`.
///
/// Lower half: `0 ≤ ofNat i` ([`zero_le_of_nat`]) times `0 ≤ Δ`
/// ([`delta_nonneg_of`]) gives `0 ≤ ofNat i · Δ` (`mul_nonneg`), and
/// [`shift_le_of_nonneg`] turns that into `a ≤ a + ofNat i · Δ`.
///
/// Upper half: `i < succ m` gives `i ≤ succ m` ([`nat_le_of_lt`]), so `ofNat i
/// ≤ ofNat (succ m)` ([`CRealPrelude::of_nat_le`]); multiplying through by the
/// nonneg `Δ` (`mul_le_mul_of_nonneg_left`, commuted to put `Δ` on the right
/// the same way `riemannSum_le`'s own pointwise step does) gives `ofNat i · Δ
/// ≤ ofNat (succ m) · Δ`, and `ofNat (succ m) · Δ ~ b − a` exactly
/// ([`mesh_times_count_eq_width`]), so `ofNat i · Δ ≤ b − a`; adding `a` to
/// both sides and folding `a + (b − a) ~ b` ([`add_sub_cancel`]) gives `a +
/// ofNat i · Δ ≤ b`.
fn declare_riemann_sample_in_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let n = d.succ(m);
    let hlt_ty = d.lt(i, n);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);

    let (delta, delta_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let sp = sample_point(d, p, a, delta, i);
    let of_nat_i = d.const_app(p.of_nat, &[i]);
    let term = cmul(d, p, of_nat_i, delta); // mul (ofNat i) delta, defeq (sp - a)'s summand

    // lower : le a sp.
    let lower = {
        let i_nonneg = zero_le_of_nat(d, p, i);
        let term_nonneg = d.lemma(p.mul_nonneg, &[of_nat_i, delta, i_nonneg, delta_nonneg]);
        shift_le_of_nonneg(d, p, a, term, term_nonneg)
    };

    // upper : le sp b.
    let upper = {
        let hle_i_n = nat_le_of_lt(d, i, n, hlt);
        let of_nat_ile = d.lemma(p.of_nat_le, &[i, n, hle_i_n]); // le (ofNat i) (ofNat n)
        let of_nat_n = d.const_app(p.of_nat, &[n]);

        let step = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[delta, of_nat_i, of_nat_n, delta_nonneg, of_nat_ile],
        );
        // step : le (mul delta (ofNat i)) (mul delta (ofNat n))
        let comm_i = d.lemma(p.mul_comm, &[delta, of_nat_i]);
        let comm_n = d.lemma(p.mul_comm, &[delta, of_nat_n]);
        let di = cmul(d, p, delta, of_nat_i);
        let dn = cmul(d, p, delta, of_nat_n);
        let nd = cmul(d, p, of_nat_n, delta);
        let commuted = d.lemma(p.le_congr, &[di, term, dn, nd, comm_i, comm_n, step]);
        // commuted : le (mul (ofNat i) delta) (mul (ofNat n) delta) = le term nd

        let width = width_of(d, p, a, b);
        let one_nat = d.num(1);
        let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
        let frac_real = embed(d, p, frac);
        let n_delta_eq_width = mesh_times_count_eq_width(d, p, width, frac_real, m);
        // n_delta_eq_width : Equiv (mul (ofNat n) delta) width -- nd, syntactically

        let refl_term = d.lemma(p.equiv_refl, &[term]);
        let term_le_width = d.lemma(
            p.le_congr,
            &[term, term, nd, width, refl_term, n_delta_eq_width, commuted],
        );
        // term_le_width : le term width

        let refl_a = d.lemma(p.le_refl, &[a]);
        let shifted = d.lemma(p.add_le_add, &[a, a, term, width, refl_a, term_le_width]);
        // shifted : le (add a term) (add a width) = le sp (add a width)

        let cancel = add_sub_cancel(d, p, a, b); // Equiv (add a width) b
        let a_width = cadd(d, p, a, width);
        let refl_sp = d.lemma(p.equiv_refl, &[sp]);
        d.lemma(p.le_congr, &[sp, sp, a_width, b, refl_sp, cancel, shifted])
        // : le sp b
    };

    let a_le_sp = cle(d, p, a, sp);
    let sp_le_b = cle(d, p, sp, b);
    let and_ty = d.const_app(p.rat.int.logic.and, &[a_le_sp, sp_le_b]);
    let proof_body = and_intro(d, p, a_le_sp, sp_le_b, lower, upper);

    let ty = {
        let after_hlt = d.arrow(hlt_ty, and_ty);
        let after_hab = d.arrow(hab_ty, after_hlt);
        let over_i = d.pi_fv(i_fv, nat, after_hab);
        let over_m = d.pi_fv(m_fv, nat, over_i);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, proof_body);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hlt);
        let over_i = d.lam_fv(i_fv, nat, with_hab);
        let over_m = d.lam_fv(m_fv, nat, over_i);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        d.lam_fv(a_fv, carrier, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sample_in_bounds,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.riemannSum_le_on : ∀ f g a b m, le a b → (∀ z, le a z → le z b → le
/// (f z) (g z)) → le (riemannSum f a b m) (riemannSum g a b m)` —
/// [`declare_riemann_sum_le`]'s pointwise hypothesis RESTRICTED to `[a, b]`.
/// **`riemannSum_le` itself is unchanged** — both theorems exist, stated
/// exactly as their own doc comments say, per the module documentation.
///
/// Identical scaffolding to `declare_riemann_sum_le`; the only change is
/// inside `bounded_pointwise`: the `i < n` witness the original already
/// threads through for `sum_range_le`'s own signature (there, discarded) is
/// used here to invoke [`declare_riemann_sample_in_bounds`]'s theorem at
/// `(a, b, m, i, hab, hlt)`, and `And.left`/`And.right` split its conclusion
/// into the two bounds `hfg` now needs.
fn declare_riemann_sum_le_on(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    // hfg_ty := ∀ z, le a z → le z b → le (f z) (g z) -- RESTRICTED to [a, b],
    // unlike `declare_riemann_sum_le`'s global `∀ z, le (f z) (g z)`.
    let hfg_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let conclusion = cle(d, p, fz, gz);
        let z_le_b = cle(d, p, z, b);
        let after_upper = d.arrow(z_le_b, conclusion);
        let a_le_z = cle(d, p, a, z);
        let after_lower = d.arrow(a_le_z, after_upper);
        d.pi_fv(z_fv, carrier, after_lower)
    };
    let hfg_fv = d.fresh_fvar();
    let hfg = d.kernel().fvar(hfg_fv);

    let (delta, delta_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let n = d.succ(m);

    let f_summand = summand_fn(d, p, f, a, delta);
    let g_summand = summand_fn(d, p, g, a, delta);

    let bounded_pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = sample_point(d, p, a, delta, i);
        let fz = d.apply(f, &[sp]);
        let gz = d.apply(g, &[sp]);

        let lt_hyp_ty = d.lt(i, n);
        let lt_fv = d.fresh_fvar();
        let lt = d.kernel().fvar(lt_fv);

        // and_bounds : And (le a sp) (le sp b), from
        // `riemannSum_sample_in_bounds a b m i hab lt`.
        let and_bounds = d.const_app(p.riemann_sample_in_bounds, &[a, b, m, i, hab, lt]);
        let a_le_sp = cle(d, p, a, sp);
        let sp_le_b = cle(d, p, sp, b);
        let lower = d.const_app(logic.and_left, &[a_le_sp, sp_le_b, and_bounds]);
        let upper = d.const_app(logic.and_right, &[a_le_sp, sp_le_b, and_bounds]);
        let h_fg = d.apply(hfg, &[sp, lower, upper]); // le (f sp) (g sp)

        let step = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[delta, fz, gz, delta_nonneg, h_fg],
        );
        // step : le (mul delta fz) (mul delta gz)
        let comm_f = d.lemma(p.mul_comm, &[delta, fz]); // Equiv (mul delta fz) (mul fz delta)
        let comm_g = d.lemma(p.mul_comm, &[delta, gz]);
        let df = cmul(d, p, delta, fz);
        let dg = cmul(d, p, delta, gz);
        let fd = cmul(d, p, fz, delta);
        let gd = cmul(d, p, gz, delta);
        let transported = d.lemma(p.le_congr, &[df, fd, dg, gd, comm_f, comm_g, step]);
        // transported : le (mul fz delta) (mul gz delta) = le (f_summand i) (g_summand i)

        let with_lt = d.lam_fv(lt_fv, lt_hyp_ty, transported);
        d.lam_fv(i_fv, nat, with_lt)
    };

    let result = d.lemma(
        p.sum_range_le,
        &[f_summand, g_summand, n, bounded_pointwise],
    );

    let ty = {
        let lhs_rs = rsum(d, p, f, a, b, m);
        let rhs_rs = rsum(d, p, g, a, b, m);
        cle(d, p, lhs_rs, rhs_rs)
    };
    let ty_inner = {
        let after_hfg = d.arrow(hfg_ty, ty);
        d.arrow(hab_ty, after_hfg)
    };
    let ty_full = {
        let over_m = d.pi_fv(m_fv, nat, ty_inner);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_g = d.pi_fv(g_fv, f_ty, over_a);
        d.pi_fv(f_fv, f_ty, over_g)
    };
    let value_inner = {
        let with_hfg = d.lam_fv(hfg_fv, hfg_ty, result);
        d.lam_fv(hab_fv, hab_ty, with_hfg)
    };
    let value_full = {
        let over_m = d.lam_fv(m_fv, nat, value_inner);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_g = d.lam_fv(g_fv, f_ty, over_a);
        d.lam_fv(f_fv, f_ty, over_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_le_on,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

// --- `riemannSum_const` --------------------------------------------------

/// `Equiv (ofNat (Nat.succ Nat.zero)) one` — `CReal.ofNat 1 ~ CReal.one`.
///
/// A local restatement of `derivative.rs`'s private `of_nat_one_equiv`
/// (that file is out of scope for this slice, so it cannot be called from
/// here): `ofNat 1 := ofRat (Rat.natDivSucc 1 0)` unfolds one delta step,
/// `one := ofRat Rat.one` unfolds one delta step the same way, and what
/// bridges them is `Eq Rat (Rat.natDivSucc 1 0) Rat.one`
/// ([`CRealPrelude::rat_unit_eq_one`]), lifted across `ofRat` by
/// [`rat_eq_rewrite`].
fn of_nat_one_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let one_rat = rone(d, rat);
    let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]); // Eq Rat unit one_rat
    let unit_embed = embed(d, p, unit); // defeq (ofNat 1)
    let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
    rat_eq_rewrite(d, unit, one_rat, unit_eq_one, refl_start, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, unit_embed, embedded)
    })
    // : Equiv unit_embed (ofRat one_rat) -- defeq Equiv (ofNat 1) one.
}

/// `Equiv (ofNat (Nat.succ m)) (add (ofNat m) one)` — the successor law
/// `CReal.ofNat` carries no equation for.
///
/// A local restatement of `derivative.rs`'s private `of_nat_succ_equiv`,
/// for the same out-of-scope-file reason as [`of_nat_one_equiv_local`]:
/// built from [`RatPrelude::nat_div_succ_add`] (`natDivSucc m 0 +
/// natDivSucc 1 0 = natDivSucc (Nat.add m 1) 0`, with `Nat.add m 1` defeq
/// `Nat.succ m`) plus [`CRealPrelude::of_rat_add`] to lift the rational sum
/// across `ofRat`, then [`of_nat_one_equiv_local`] to fold the second
/// summand from `ofNat 1` down to `one`.
fn of_nat_succ_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let one_c = d.kernel().const_(p.one, vec![]);

    let m_rat = d.const_app(rat.nat_div_succ, &[m, zero_nat]);
    let one_ratdiv = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let sum_rat = radd(d, m_rat, one_ratdiv);
    let succ_m = d.succ(m);
    let succ_rat = d.const_app(rat.nat_div_succ, &[succ_m, zero_nat]);
    // Eq Rat sum_rat (natDivSucc (Nat.add m 1) 0), the RHS defeq succ_rat.
    let add_eq = d.lemma(rat.nat_div_succ_add, &[m, one_nat, zero_nat]);

    let of_nat_m = d.const_app(p.of_nat, &[m]);
    let of_nat_1 = d.const_app(p.of_nat, &[one_nat]);
    let of_nat_succ_m = d.const_app(p.of_nat, &[succ_m]);
    let add_of_nat_m_1 = cadd(d, p, of_nat_m, of_nat_1);

    // Equiv (add of_nat_m of_nat_1) (ofRat sum_rat)
    let add_step = d.lemma(p.of_rat_add, &[m_rat, one_ratdiv]);
    // Equiv (add of_nat_m of_nat_1) (ofRat succ_rat) -- defeq (ofNat (succ m))
    let rewritten = rat_eq_rewrite(d, sum_rat, succ_rat, add_eq, add_step, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, add_of_nat_m_1, embedded)
    });
    // Equiv (ofNat (succ m)) (add of_nat_m of_nat_1)
    let flipped = d.lemma(p.equiv_symm, &[add_of_nat_m_1, of_nat_succ_m, rewritten]);

    // Equiv (add of_nat_m of_nat_1) (add of_nat_m one)
    let one_eq = of_nat_one_equiv_local(d, p);
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
    // : Equiv (ofNat (succ m)) (add (ofNat m) one)
}

/// `Eq Rat (Rat.mul (Rat.natDivSucc (Nat.succ m) 0) (Rat.natDivSucc 1 m))
/// Rat.one` — `(m+1)/1 · 1/(m+1) = 1`.
///
/// The same rational identity `rat_prelude/field.rs::declare_inv_nat_div_succ`
/// derives in passing as its own `cancel` step (`w·c = 1`, with `w :=
/// (m+1)/1` and `c := 1/(m+1)`): `nat_div_succ_mul` fuses the product into a
/// single `natDivSucc`, `Nat.mul_one` collapses its numerator, then
/// `nat_div_succ_scale` at index `0` (composed with `Nat.zero_add`) reads
/// the result as `1/1`, and [`CRealPrelude::rat_unit_eq_one`] closes `1/1 =
/// Rat.one` — reusing that already-proved fact in place of a fresh
/// `self_normalize` call. `field.rs`'s own proof continues past this point
/// to compute `(1/(m+1))⁻¹`; this stops at the product identity, which is
/// all `mesh_inverse_identity` below needs.
fn nat_div_succ_inverse_pair_eq_one(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let nat = rat.int.nat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let successor = d.succ(m);
    let modulus = d.const_app(rat.nat_div_succ, &[one_nat, m]);
    let whole = d.const_app(rat.nat_div_succ, &[successor, zero_nat]);
    let one_val = rone(d, rat);

    let product = rmul(d, whole, modulus);
    let fused = {
        let scaled = NatOps::mul(d, successor, one_nat);
        d.const_app(rat.nat_div_succ, &[scaled, m])
    };
    let fuse = d.lemma(rat.nat_div_succ_mul, &[successor, one_nat, m]);
    let collapsed = d.const_app(rat.nat_div_succ, &[successor, m]);
    let collapse = {
        let scaled = NatOps::mul(d, successor, one_nat);
        let identity = d.lemma(nat.mul_one, &[successor]);
        nat_eq_to_rat(d, scaled, successor, identity, &|d, t| {
            d.const_app(rat.nat_div_succ, &[t, m])
        })
    };
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let scale = {
        let deep = NatOps::mul(d, successor, zero_nat);
        let index = NatOps::add(d, deep, m);
        let law = d.lemma(rat.nat_div_succ_scale, &[m, zero_nat]);
        let flatten = d.lemma(nat.zero_add, &[m]);
        nat_rewrite_prop(d, index, m, flatten, law, &|d, t| {
            let left = d.const_app(rat.nat_div_succ, &[successor, t]);
            req(d, left, unit)
        })
    };
    let unit_is_one = d.lemma(p.rat_unit_eq_one, &[]);
    let (_, cancel) = rchain(
        d,
        product,
        &[
            (fused, fuse),
            (collapsed, collapse),
            (unit, scale),
            (one_val, unit_is_one),
        ],
    );
    cancel
    // : Eq Rat (rmul whole modulus) one_val
}

/// `Equiv (mul (ofNat (Nat.succ m)) (ofRat (Rat.natDivSucc 1 m))) one` —
/// the mesh count exactly cancels the mesh fraction, for every `m`.
///
/// `ofNat (succ m)` and `ofRat (natDivSucc 1 m)` are each one delta step
/// from an `embed` of the corresponding `Rat.natDivSucc`; `CReal.ofRat_mul`
/// lifts [`nat_div_succ_inverse_pair_eq_one`]'s product identity across
/// that embedding, landing on `embed Rat.one`, itself one delta step from
/// `CReal.one`.
fn mesh_inverse_identity(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let successor = d.succ(m);
    let modulus = d.const_app(rat.nat_div_succ, &[one_nat, m]);
    let whole = d.const_app(rat.nat_div_succ, &[successor, zero_nat]);

    let embed_whole = embed(d, p, whole); // defeq (ofNat (succ m))
    let embed_modulus = embed(d, p, modulus); // defeq (ofRat (natDivSucc 1 m))
    let product_real = cmul(d, p, embed_whole, embed_modulus);

    let rat_eq = nat_div_succ_inverse_pair_eq_one(d, p, m); // Eq Rat (rmul whole modulus) one_rat
    let of_rat_mul_step = d.lemma(p.of_rat_mul, &[whole, modulus]);
    // : Equiv product_real (embed (rmul whole modulus))

    let product_rat = rmul(d, whole, modulus);
    let one_rat = rone(d, rat);
    rat_eq_rewrite(d, product_rat, one_rat, rat_eq, of_rat_mul_step, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, product_real, embedded)
    })
    // : Equiv product_real (embed one_rat) -- defeq Equiv product_real one.
}

/// `Equiv (sumRange (fun _ => w) (Nat.succ m)) (mul (ofNat (Nat.succ m)) w)`
/// — `succ m` copies of a constant `w` sum to `(succ m)·w`. Induction on
/// `m`, `w` fixed.
///
/// The base case (`m = 0`) needs `ofNat 1 ~ one`
/// ([`of_nat_one_equiv_local`]); the step needs `ofNat (succ k) ~ add
/// (ofNat k) one` ([`of_nat_succ_equiv_local`]) plus [`right_distrib`] to
/// expand `(ofNat k + one)·w`. Both hold for every `m`/`k` directly (no
/// induction of their own), so inducting on `m` here — rather than on the
/// subinterval COUNT `n` from `Nat.zero` — never needs an `ofNat 0` fact at
/// all, which `CReal.ofNat` (defined via `Rat.natDivSucc _ 0`, not
/// `Nat.rec`) does not give for free.
fn riemann_sum_const_core(d: &mut IntDev<'_>, p: CRealPrelude, w: ExprId, m: ExprId) -> ExprId {
    let const_fn = |d: &mut IntDev<'_>| -> ExprId {
        let i_fv = d.fresh_fvar();
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, w)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let f = const_fn(d);
        let sx = d.succ(x);
        let lhs = d.const_app(p.sum_range, &[f, sx]);
        let ox = d.const_app(p.of_nat, &[sx]);
        let rhs = cmul(d, p, ox, w);
        equiv(d, p, lhs, rhs)
    };

    d.induct(
        &motive,
        &|d| {
            // Goal (defeq unfolded): Equiv (add zero w) (mul (ofNat 1) w).
            let zero_c = czero(d, p);
            let one_c = d.kernel().const_(p.one, vec![]);
            let one_nat = d.num(1);
            let of_nat_1 = d.const_app(p.of_nat, &[one_nat]);

            let start = cadd(d, p, zero_c, w);
            let m1w = cmul(d, p, one_c, w);
            let target_mw = cmul(d, p, of_nat_1, w);

            // add zero w ~ w
            let step1 = {
                let comm = d.lemma(p.add_comm, &[zero_c, w]); // add zero w ~ add w zero
                let wz = cadd(d, p, w, zero_c);
                let vanish = d.lemma(p.add_zero, &[w]); // add w zero ~ w
                d.lemma(p.equiv_trans, &[start, wz, w, comm, vanish])
            };
            // w ~ mul one w
            let step2 = {
                let mw1 = cmul(d, p, w, one_c);
                let mul_one_w = d.lemma(p.mul_one, &[w]); // mul w one ~ w
                let back = d.lemma(p.equiv_symm, &[mw1, w, mul_one_w]); // w ~ mul w one
                let comm = d.lemma(p.mul_comm, &[w, one_c]); // mul w one ~ mul one w
                d.lemma(p.equiv_trans, &[w, mw1, m1w, back, comm])
            };
            // mul one w ~ mul (ofNat 1) w
            let step3 = {
                let one_eq = of_nat_one_equiv_local(d, p); // Equiv (ofNat 1) one
                let back = d.lemma(p.equiv_symm, &[of_nat_1, one_c, one_eq]); // one ~ ofNat 1
                let refl_w = d.lemma(p.equiv_refl, &[w]);
                d.lemma(p.mul_congr, &[one_c, of_nat_1, w, w, back, refl_w])
            };
            let s01 = d.lemma(p.equiv_trans, &[start, w, m1w, step1, step2]);
            d.lemma(p.equiv_trans, &[start, m1w, target_mw, s01, step3])
        },
        &|d, j, ih| {
            // ih : Equiv (sumRange f (succ j)) (mul (ofNat (succ j)) w)
            // Goal (defeq unfolded): Equiv (add (sumRange f (succ j)) w)
            //   (mul (ofNat (succ (succ j))) w)
            let f = const_fn(d);
            let sj = d.succ(j);
            let prior = d.const_app(p.sum_range, &[f, sj]);
            let start = cadd(d, p, prior, w);

            let of_nat_sj = d.const_app(p.of_nat, &[sj]);
            let ih_target = cmul(d, p, of_nat_sj, w);

            // start ~ add ih_target w
            let step_ih = {
                let refl_w = d.lemma(p.equiv_refl, &[w]);
                d.lemma(p.add_congr, &[prior, ih_target, w, w, ih, refl_w])
            };
            let after_ih = cadd(d, p, ih_target, w);

            let ssj = d.succ(sj);
            let of_nat_ssj = d.const_app(p.of_nat, &[ssj]);
            let final_target = cmul(d, p, of_nat_ssj, w);

            let one_c = d.kernel().const_(p.one, vec![]);
            let succ_eq = of_nat_succ_equiv_local(d, p, sj); // Equiv (ofNat (succ sj)) (add (ofNat sj) one)
            let sum_of_nat = cadd(d, p, of_nat_sj, one_c);
            let expanded = cmul(d, p, sum_of_nat, w);

            // final_target ~ expanded
            let h_a = {
                let refl_w = d.lemma(p.equiv_refl, &[w]);
                d.lemma(
                    p.mul_congr,
                    &[of_nat_ssj, sum_of_nat, w, w, succ_eq, refl_w],
                )
            };
            // expanded ~ add ih_target (mul one w)
            let h_b = right_distrib(d, p, of_nat_sj, one_c, w);
            let one_w = cmul(d, p, one_c, w);
            let distributed = cadd(d, p, ih_target, one_w);
            // distributed ~ after_ih
            let h_c = {
                let refl_left = d.lemma(p.equiv_refl, &[ih_target]);
                let one_mul_w = {
                    // Equiv (mul one w) w
                    let mw1 = cmul(d, p, w, one_c);
                    let mul_one_w = d.lemma(p.mul_one, &[w]);
                    let comm = d.lemma(p.mul_comm, &[one_c, w]); // mul one w ~ mul w one
                    d.lemma(p.equiv_trans, &[one_w, mw1, w, comm, mul_one_w])
                };
                d.lemma(
                    p.add_congr,
                    &[ih_target, ih_target, one_w, w, refl_left, one_mul_w],
                )
            };

            let rev = {
                let s1 = d.lemma(
                    p.equiv_trans,
                    &[final_target, expanded, distributed, h_a, h_b],
                );
                d.lemma(
                    p.equiv_trans,
                    &[final_target, distributed, after_ih, s1, h_c],
                )
            };
            let rev_flipped = d.lemma(p.equiv_symm, &[final_target, after_ih, rev]);
            d.lemma(
                p.equiv_trans,
                &[start, after_ih, final_target, step_ih, rev_flipped],
            )
        },
        m,
    )
}

/// `Equiv (mul (ofNat (Nat.succ m)) w) (mul c width)` where `w := mul c
/// delta` and `delta := mul width frac` — the algebraic rearrangement that
/// closes [`declare_riemann_sum_const`] once [`riemann_sum_const_core`] has
/// collapsed the sum. An eight-step associativity/commutativity chain
/// exposes `mul (ofNat (succ m)) frac` next to `width`, cancels it via
/// [`mesh_inverse_identity`], then folds the trailing `mul _ one` via
/// `mul_one`.
#[allow(clippy::too_many_arguments)]
fn riemann_sum_const_rearrange(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    width: ExprId,
    frac: ExprId,
    m: ExprId,
) -> ExprId {
    let on = {
        let successor = d.succ(m);
        d.const_app(p.of_nat, &[successor]) // ofNat (succ m)
    };
    let one_c = d.kernel().const_(p.one, vec![]);

    let delta = cmul(d, p, width, frac);
    let w = cmul(d, p, c, delta);
    let a_start = cmul(d, p, on, w); // mul (ofNat n) (mul c (mul width frac))

    let on_c = cmul(d, p, on, c);
    let c_on = cmul(d, p, c, on);
    let on_width = cmul(d, p, on, width);
    let width_on = cmul(d, p, width, on);
    let on_frac = cmul(d, p, on, frac);
    let on_delta = cmul(d, p, on, delta);
    let width_on_frac = cmul(d, p, width_on, frac);
    let width_one = cmul(d, p, width, one_c);
    let width_on_frac_paren = cmul(d, p, width, on_frac);

    // b1 := mul (mul on c) delta
    let b1 = cmul(d, p, on_c, delta);
    // h1 : a_start ~ b1
    let h1 = {
        let assoc = d.lemma(p.mul_assoc, &[on, c, delta]); // Equiv b1 a_start
        d.lemma(p.equiv_symm, &[b1, a_start, assoc])
    };

    // b2 := mul (mul c on) delta
    let b2 = cmul(d, p, c_on, delta);
    // h2 : b1 ~ b2
    let h2 = {
        let comm = d.lemma(p.mul_comm, &[on, c]); // Equiv on_c c_on
        let refl_delta = d.lemma(p.equiv_refl, &[delta]);
        d.lemma(p.mul_congr, &[on_c, c_on, delta, delta, comm, refl_delta])
    };

    // b3 := mul c (mul on delta)
    let b3 = cmul(d, p, c, on_delta);
    // h3 : b2 ~ b3
    let h3 = d.lemma(p.mul_assoc, &[c, on, delta]);

    // b4 := mul c (mul (mul on width) frac)
    let on_width_frac = cmul(d, p, on_width, frac);
    let b4 = cmul(d, p, c, on_width_frac);
    // h4 : b3 ~ b4
    let h4 = {
        let assoc = d.lemma(p.mul_assoc, &[on, width, frac]); // Equiv on_width_frac on_delta
        let inner = d.lemma(p.equiv_symm, &[on_width_frac, on_delta, assoc]);
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(p.mul_congr, &[c, c, on_delta, on_width_frac, refl_c, inner])
    };

    // b5 := mul c (mul (mul width on) frac)
    let b5 = cmul(d, p, c, width_on_frac);
    // h5 : b4 ~ b5
    let h5 = {
        let comm = d.lemma(p.mul_comm, &[on, width]); // Equiv on_width width_on
        let refl_frac = d.lemma(p.equiv_refl, &[frac]);
        let inner = d.lemma(
            p.mul_congr,
            &[on_width, width_on, frac, frac, comm, refl_frac],
        );
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(
            p.mul_congr,
            &[c, c, on_width_frac, width_on_frac, refl_c, inner],
        )
    };

    // b6 := mul c (mul width (mul on frac))
    let b6 = cmul(d, p, c, width_on_frac_paren);
    // h6 : b5 ~ b6
    let h6 = {
        let assoc = d.lemma(p.mul_assoc, &[width, on, frac]); // Equiv width_on_frac width_on_frac_paren
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(
            p.mul_congr,
            &[c, c, width_on_frac, width_on_frac_paren, refl_c, assoc],
        )
    };

    // b7 := mul c (mul width one)
    let b7 = cmul(d, p, c, width_one);
    // h7 : b6 ~ b7
    let h7 = {
        let cancel = mesh_inverse_identity(d, p, m); // Equiv on_frac one_c
        let refl_width = d.lemma(p.equiv_refl, &[width]);
        let inner = d.lemma(
            p.mul_congr,
            &[width, width, on_frac, one_c, refl_width, cancel],
        );
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(
            p.mul_congr,
            &[c, c, width_on_frac_paren, width_one, refl_c, inner],
        )
    };

    // b8 := mul c width
    let b8 = cmul(d, p, c, width);
    // h8 : b7 ~ b8
    let h8 = {
        let mul_one_w = d.lemma(p.mul_one, &[width]); // Equiv width_one width
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(p.mul_congr, &[c, c, width_one, width, refl_c, mul_one_w])
    };

    echain(
        d,
        p,
        a_start,
        &[
            (b1, h1),
            (b2, h2),
            (b3, h3),
            (b4, h4),
            (b5, h5),
            (b6, h6),
            (b7, h7),
            (b8, h8),
        ],
    )
}

/// Chain `Equiv start …` through `(next, step)` pairs — a private restatement
/// of `ring_helpers.rs`'s `echain`, `pub(super)` there and unreachable from
/// this out-of-scope-for-this-slice file for the same reason as
/// [`of_nat_one_equiv_local`].
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

/// `CReal.riemannSum_const : ∀ c a b m,
/// Equiv (riemannSum (fun _ => c) a b m) (mul c (add b (neg a)))` — a
/// constant function's Riemann sum is exactly base times height, for every
/// subinterval count `m`. See the module documentation for the two-piece
/// route.
fn declare_riemann_sum_const(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let f_const = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, c)
    };

    let width = width_of(d, p, a, b);
    let frac = {
        let one_nat = d.num(1);
        let rat_frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
        embed(d, p, rat_frac)
    };
    let delta = cmul(d, p, width, frac); // defeq delta_of(a, b, m)
    let w = cmul(d, p, c, delta);

    // step1 : Equiv (riemannSum f_const a b m) (mul (ofNat (succ m)) w)
    let step1 = riemann_sum_const_core(d, p, w, m);

    // step2 : Equiv (mul (ofNat (succ m)) w) (mul c width)
    let step2 = riemann_sum_const_rearrange(d, p, c, width, frac, m);

    let successor = d.succ(m);
    let of_nat_n = d.const_app(p.of_nat, &[successor]);
    let a_mid = cmul(d, p, of_nat_n, w);
    let lhs = rsum(d, p, f_const, a, b, m);
    let rhs = cmul(d, p, c, width);

    let proof = d.lemma(p.equiv_trans, &[lhs, a_mid, rhs, step1, step2]);

    let ty = equiv(d, p, lhs, rhs);
    let ty_full = {
        let over_m = d.pi_fv(m_fv, nat, ty);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(c_fv, carrier, over_a)
    };
    let value_full = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(c_fv, carrier, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_const,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

// --- `CReal.sumRange_double` -- toward `riemannSum_cauchy` -----------------
//
// The refinement estimate `riemannSum_cauchy` needs (see this module's own
// top-level documentation for the paper estimate) compares `riemannSum f a b
// m` at two DIFFERENT subdivision counts. The standard route is a common
// refinement of both partitions; for the special case of doubling the count
// (`m` pieces vs. `2m` pieces, each of the coarse pieces split into two equal
// fine pieces), the needed bookkeeping reduces to a single fact about
// `CReal.sumRange` that mentions no Riemann sum at all: summing `2k` terms of
// an arbitrary `g : Nat -> CReal` and grouping them two at a time gives the
// same total as summing the `k` pairwise sums. That fact is
// [`declare_sum_range_double`], proved directly by induction on `k` (no
// hypothesis on `g` needed — this is pure regrouping, not an estimate), and
// it is landed here as a standalone, reusable building block ahead of the
// error-bound machinery `riemannSum_cauchy` itself still needs (bounding each
// pair's contribution against the coarse term via
// `CReal.UniformlyContinuousOn.spec`, at a subdivision count large enough for
// the outer accuracy via the same magnitude/`e_acc` scaling
// `monotone_of_nonneg_deriv` uses, then folding the resulting sum-of-bounds
// via `CReal.sumRange_le` + `CReal.sumRange_const` + `CReal.mesh_count_width`
// into a single real inequality, and finally converting that real inequality
// into the `CReal.Within`-shaped bound `CReal.Cauchy` demands at `riemannSum`'s
// own canonical sample indices — none of which is attempted here).

/// `fun i => add (g (Nat.mul 2 i)) (g (Nat.succ (Nat.mul 2 i)))` — the
/// `i`-th block of two consecutive `g`-terms, `g(2i) + g(2i+1)`.
/// `fun k => f (Nat.add m k)` — `f` shifted by `m`. Reproduced verbatim from
/// `series.rs::shifted_fn` / `geometric.rs::shifted_fn` (both private to
/// their own modules), matching `CReal.sumRange_split`'s own instantiated
/// conclusion shape exactly so this file's block sums are structurally
/// (not merely propositionally) the same closures `sum_range_split`
/// produces.
fn reblock_shifted_fn(d: &mut IntDev<'_>, m: ExprId, f: ExprId) -> ExprId {
    let nat_add = d.prelude().add;
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let mk = d.const_app(nat_add, &[m, k]);
    let body = d.apply(f, &[mk]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}
/// `fun i => sumRange (fun j => g (Nat.add (Nat.mul bs i) j)) bs` — the
/// `i`-th block of `bs` consecutive `g`-terms, starting at `bs * i`. `bs` is
/// always the FIRST argument of `Nat.mul` here, matching the shape
/// `Nat.mul`'s own iota-reduction forces at the induction step below (never
/// `Nat.mul i bs`, which is only propositionally, not definitionally, the
/// same term).
fn reblock_block(d: &mut IntDev<'_>, p: CRealPrelude, g: ExprId, bs: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let offset = NatOps::mul(d, bs, i);
    let shifted = reblock_shifted_fn(d, offset, g);
    let body = d.const_app(p.sum_range, &[shifted, bs]);
    d.lam_fv(i_fv, nat, body)
}
/// The proof term for `CReal.sumRange_reblock` at a fixed block size `bs`,
/// by induction on the block count `k`. See this section's own module
/// documentation for the derivation.
fn sum_range_reblock_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    g: ExprId,
    bs: ExprId,
    k: ExprId,
) -> ExprId {
    let block = reblock_block(d, p, g, bs);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let total = NatOps::mul(d, bs, x);
        let lhs = d.const_app(p.sum_range, &[g, total]);
        let rhs = d.const_app(p.sum_range, &[block, x]);
        equiv(d, p, lhs, rhs)
    };

    d.induct(
        &motive,
        &|d| {
            // motive(zero): `Nat.mul bs Nat.zero ≡ Nat.zero`, so both sides
            // reduce (defeq) to `CReal.zero`.
            let zero_c = czero(d, p);
            d.lemma(p.equiv_refl, &[zero_c])
        },
        &|d, j, ih| {
            // ih : Equiv (sumRange g (mul bs j)) (sumRange block j)
            let bs_j = NatOps::mul(d, bs, j);
            let succ_j = d.succ(j);

            let sum_g_bsj = d.const_app(p.sum_range, &[g, bs_j]);
            let sum_block_j = d.const_app(p.sum_range, &[block, j]);
            let block_j = d.apply(block, &[j]);

            // split_step : Equiv (sumRange g (add bs_j bs))
            //                    (add sum_g_bsj (sumRange (shifted bs_j g) bs))
            // -- the second summand is defeq `block_j` (`reblock_block`'s own
            // definition at `i := j`, same `bs_j` offset, same block size
            // `bs`) by one beta step, no new lemma needed.
            let split_step = d.lemma(p.sum_range_split, &[g, bs_j, bs]);

            // h1 : Equiv (add sum_g_bsj block_j) (add sum_block_j block_j)
            let refl_block_j = d.lemma(p.equiv_refl, &[block_j]);
            let h1 = d.lemma(
                p.add_congr,
                &[sum_g_bsj, sum_block_j, block_j, block_j, ih, refl_block_j],
            );

            // Goal (defeq unfolded, `succ_j`): `Equiv (sumRange g (mul bs
            // succ_j)) (sumRange block succ_j)` -- `mul bs succ_j` is defeq
            // `add bs_j bs` (`Nat.mul`'s iota step), and `sumRange block
            // succ_j` is defeq `add sum_block_j block_j` (`sumRange`'s own
            // iota step), so `equiv_trans(split_step, h1)` closes it exactly.
            let lhs_goal = {
                let total_succ = NatOps::mul(d, bs, succ_j);
                d.const_app(p.sum_range, &[g, total_succ])
            };
            let mid = cadd(d, p, sum_g_bsj, block_j);
            let rhs_goal = d.const_app(p.sum_range, &[block, succ_j]);

            d.lemma(p.equiv_trans, &[lhs_goal, mid, rhs_goal, split_step, h1])
        },
        k,
    )
}
/// `CReal.sumRange_reblock : ∀ (g : Nat → CReal) (n k : Nat), Equiv (sumRange
/// g (Nat.mul (Nat.succ n) k)) (sumRange (fun i => sumRange (fun j => g
/// (Nat.add (Nat.mul (Nat.succ n) i) j)) (Nat.succ n)) k)` — regrouping
/// `k · (n+1)` consecutive terms of an arbitrary `g` into `k` consecutive
/// blocks of `n+1`, exactly (no error term), for an arbitrary block size
/// `n+1` (never zero). Generalizes `CReal.sumRange_double` (block size fixed
/// at the literal `2`) from a private, not-yet-merged worktree branch; see
/// this section's own module documentation for the derivation and precisely
/// what remains toward `riemannSum_cauchy`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_sum_range_reblock(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let bs = d.succ(n);
    let proof = sum_range_reblock_proof(d, p, g, bs, k);

    let ty = {
        let total = NatOps::mul(d, bs, k);
        let lhs = d.const_app(p.sum_range, &[g, total]);
        let block = reblock_block(d, p, g, bs);
        let rhs = d.const_app(p.sum_range, &[block, k]);
        equiv(d, p, lhs, rhs)
    };
    let ty_full = {
        let over_k = d.pi_fv(k_fv, nat, ty);
        let over_n = d.pi_fv(n_fv, nat, over_k);
        d.pi_fv(g_fv, fn_ty, over_n)
    };
    let value_full = {
        let over_k = d.lam_fv(k_fv, nat, proof);
        let over_n = d.lam_fv(n_fv, nat, over_k);
        d.lam_fv(g_fv, fn_ty, over_n)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_reblock,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}
/// From `Rat.le (Rat.sub u v) w` and `Rat.le (Rat.sub (Rat.neg u) v) w`,
/// derive `CReal.Within u (Rat.add v w)`. Reproduced verbatim from
/// `series.rs::within_of_tail_le` / `geometric.rs::within_of_tail_le` (both
/// private to their own modules) — the RAT-LEVEL half of the bridge, already
/// fully general over any `u, v, w`.
fn within_of_sub_le(
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
/// `CReal.within_of_two_sided_le : ∀ t y : CReal, le t y → le (neg t) y →
/// ∀ i : Nat, Within (seq t i) (add (seq y i) (natDivSucc 2 i))`. See this
/// section's own module documentation for the derivation, and for whether
/// `geometric.rs::geom_tail_within` could be re-derived from this (it could,
/// without editing that file).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_within_of_two_sided_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let neg_t = cneg(d, p, t);
    let hyp1 = cle(d, p, t, y);
    let hyp2 = cle(d, p, neg_t, y);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    // `CReal.le` is a `Definition` (`le x y := ∀ n, seq x n − seq y n ≤
    // 2/(n+1)`), so `.apply(_, &[i])` unfolds it directly to the per-index
    // `Rat.le` fact -- the same idiom `geom_tail_within`'s own proof uses,
    // just at an arbitrary `i` rather than the tail's own canonical index.
    let h1_at_i = d.apply(h1, &[i]);
    let h2_at_i = d.apply(h2, &[i]);

    let u = sample(d, p, t, i);
    let v = sample(d, p, y, i);
    let w = div_succ(d, p, 2, i);

    let value_body = within_of_sub_le(d, p, u, v, w, h1_at_i, h2_at_i);

    let ty = {
        let vw = radd(d, v, w);
        let claim = within(d, p, u, vw);
        let inner = d.pi_fv(i_fv, nat, claim);
        // `h1_fv`/`h2_fv` escape into `inner` through `v`/`w` (via `y`/`i`),
        // and `t_fv`/`y_fv` escape through `hyp1`/`hyp2` -- all genuinely
        // dependent Pis (`pi_fv`), never `d.arrow`, the same trap
        // `geom_tail_within`'s own `ty` names.
        let with_h2 = d.pi_fv(h2_fv, hyp2, inner);
        let with_h1 = d.pi_fv(h1_fv, hyp1, with_h2);
        let with_y = d.pi_fv(y_fv, carrier, with_h1);
        d.pi_fv(t_fv, carrier, with_y)
    };
    let value = {
        let inner = d.lam_fv(i_fv, nat, value_body);
        let with_h2 = d.lam_fv(h2_fv, hyp2, inner);
        let with_h1 = d.lam_fv(h1_fv, hyp1, with_h2);
        let with_y = d.lam_fv(y_fv, carrier, with_h1);
        d.lam_fv(t_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.within_of_two_sided_le,
        uparams: vec![],
        ty,
        value,
    })
}

// --- roadmap step 2: an abs-bound splits into a one-sided bound -----------

/// `CReal.le_add_of_abs_sub_le : ∀ x y : CReal, ∀ q : Rat, le (abs (add x
/// (neg y))) (ofRat q) → le x (add y (ofRat q))` — roadmap step 2 toward
/// `riemannSum_cauchy`: `close_within`'s own `abs`-bound shape (exactly what
/// `UniformlyContinuousOn.spec`'s conclusion and [`declare_fine_sample_close`]
/// produce) unfolds all the way down to the CReal-level one-sided form
/// `sumRange_le`'s pointwise hypothesis needs, rather than stopping at the
/// difference-only `le (add x (neg y)) (ofRat q)`.
///
/// Route: `le_abs_self` gives `d ≤ |d|` at `d := x + (-y)`; `le_trans`
/// against the hypothesis collapses that to `d ≤ q`; `add_le_add` adds `y`
/// on the left of both sides to get `y + d ≤ y + q`; and `add_sub_cancel`
/// (this file's own ring identity, `y + (x + (-y)) ~ x`) folds the left side
/// down to exactly `x` via `le_congr`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_le_add_of_abs_sub_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny); // x + (-y)
    let abs_diff = d.const_app(p.abs, &[diff]);
    let q_embed = embed(d, p, q);
    let hyp_ty = cle(d, p, abs_diff, q_embed);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // self_le : le diff abs_diff.
    let self_le = d.lemma(p.le_abs_self, &[diff]);
    // d_le_q : le diff q_embed.
    let d_le_q = d.lemma(p.le_trans, &[diff, abs_diff, q_embed, self_le, h]);

    // grown : le (add y diff) (add y q_embed).
    let refl_y = d.lemma(p.le_refl, &[y]);
    let grown = d.lemma(p.add_le_add, &[y, y, diff, q_embed, refl_y, d_le_q]);

    // cancel : Equiv (add y diff) x -- exactly `add_sub_cancel(y, x)`'s own
    // conclusion, since `diff` IS `add x (neg y)`.
    let cancel = add_sub_cancel(d, p, y, x);

    let y_diff = cadd(d, p, y, diff);
    let yq = cadd(d, p, y, q_embed);
    let refl_yq = d.lemma(p.equiv_refl, &[yq]);
    let conclusion_proof = d.lemma(p.le_congr, &[y_diff, x, yq, yq, cancel, refl_yq, grown]);
    // conclusion_proof : le x yq.

    let ty = {
        let conclusion = cle(d, p, x, yq);
        let after_h = d.arrow(hyp_ty, conclusion);
        let over_q = d.pi_fv(q_fv, rat_carrier, after_h);
        let over_y = d.pi_fv(y_fv, carrier, over_q);
        d.pi_fv(x_fv, carrier, over_y)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, conclusion_proof);
        let over_q = d.lam_fv(q_fv, rat_carrier, with_h);
        let over_y = d.lam_fv(y_fv, carrier, over_q);
        d.lam_fv(x_fv, carrier, over_y)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.le_add_of_abs_sub_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.two_sided_of_abs_sub_le : ∀ x y : CReal, ∀ q : Rat, le (abs (add x
/// (neg y))) (ofRat q) → And (le x (add y (ofRat q))) (le y (add x (ofRat
/// q)))` — the full abs-splitting lemma the per-block Riemann sum fold's TWO
/// applications of `sumRange_le` (upper and lower) both need from a single
/// `close_within` fact, rather than calling [`declare_le_add_of_abs_sub_le`]
/// twice at swapped arguments (which would need the DIFFERENT hypothesis
/// `le (abs (add y (neg x))) (ofRat q)`, not what a `close_within x y q`
/// fact actually gives).
///
/// The first conjunct reuses [`CRealPrelude::le_add_of_abs_sub_le`] verbatim.
/// The second mirrors its route with `neg_le_abs` in place of `le_abs_self`
/// (`le (neg diff) (abs diff)` rather than `le diff (abs diff)`) and
/// [`diff_cancel_left`] in place of [`add_sub_cancel`] for the
/// add-rearrangement step.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_two_sided_of_abs_sub_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let logic = p.rat.int.logic;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny); // x + (-y)
    let ndiff = cneg(d, p, diff);
    let abs_diff = d.const_app(p.abs, &[diff]);
    let q_embed = embed(d, p, q);
    let hyp_ty = cle(d, p, abs_diff, q_embed);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let yq = cadd(d, p, y, q_embed);
    let xq = cadd(d, p, x, q_embed);

    // left : le x yq, by the already-declared theorem.
    let left = d.lemma(p.le_add_of_abs_sub_le, &[x, y, q, h]);

    // right : le y xq, the mirror via neg_le_abs.
    let right = {
        let neg_self_le = d.lemma(p.neg_le_abs, &[diff]); // le ndiff abs_diff
        let negd_le_q = d.lemma(p.le_trans, &[ndiff, abs_diff, q_embed, neg_self_le, h]);
        // negd_le_q : le ndiff q_embed

        let refl_x = d.lemma(p.le_refl, &[x]);
        let grown = d.lemma(p.add_le_add, &[x, x, ndiff, q_embed, refl_x, negd_le_q]);
        // grown : le (add x ndiff) xq

        let cancel = diff_cancel_left(d, p, x, y); // Equiv (add x ndiff) y
        let refl_xq = d.lemma(p.equiv_refl, &[xq]);
        let x_ndiff = cadd(d, p, x, ndiff);
        d.lemma(p.le_congr, &[x_ndiff, y, xq, xq, cancel, refl_xq, grown])
        // : le y xq
    };

    let left_ty = cle(d, p, x, yq);
    let right_ty = cle(d, p, y, xq);
    let conclusion_proof = and_intro(d, p, left_ty, right_ty, left, right);

    let ty = {
        let and_ty = d.const_app(logic.and, &[left_ty, right_ty]);
        let after_h = d.arrow(hyp_ty, and_ty);
        let over_q = d.pi_fv(q_fv, rat_carrier, after_h);
        let over_y = d.pi_fv(y_fv, carrier, over_q);
        d.pi_fv(x_fv, carrier, over_y)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, conclusion_proof);
        let over_q = d.lam_fv(q_fv, rat_carrier, with_h);
        let over_y = d.lam_fv(y_fv, carrier, over_q);
        d.lam_fv(x_fv, carrier, over_y)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.two_sided_of_abs_sub_le,
        uparams: vec![],
        ty,
        value,
    })
}

// --- roadmap step 3: the per-block fold ------------------------------------

/// `le (mul x z) (mul y z)` from `le zero z` and `le x y` — the missing
/// "multiply by a nonneg constant on the RIGHT" direction;
/// `mul_le_mul_of_nonneg_left` only has the constant on the left, and
/// [`summand_fn`]'s own convention (`f(x)·Δ`, value first) needs the
/// constant on the right. Built from `mul_comm` plus
/// `mul_le_mul_of_nonneg_left`, the same reuse shape [`right_distrib`] uses
/// for `left_distrib`.
fn mul_le_mul_of_nonneg_right(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    hz_nonneg: ExprId,
    hxy: ExprId,
) -> ExprId {
    let zx = cmul(d, p, z, x);
    let zy = cmul(d, p, z, y);
    let grown = d.lemma(p.mul_le_mul_of_nonneg_left, &[z, x, y, hz_nonneg, hxy]);
    // grown : le zx zy
    let xz = cmul(d, p, x, z);
    let yz = cmul(d, p, y, z);
    let c1 = d.lemma(p.mul_comm, &[z, x]); // Equiv zx xz
    let c2 = d.lemma(p.mul_comm, &[z, y]); // Equiv zy yz
    d.lemma(p.le_congr, &[zx, xz, zy, yz, c1, c2, grown])
    // : le xz yz
}

/// `fun _ : Nat => v` — a constant function of a `Nat` index. Reproduced
/// verbatim from `monotone.rs`'s private `const_fn` (that file is out of
/// scope for edits in this slice).
fn const_nat_fn(d: &mut IntDev<'_>, v: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let fv = d.fresh_fvar();
    d.lam_fv(fv, nat, v)
}

/// `Equiv (mul (ofNat (Nat.succ n)) (mul w delta_fine)) (mul w delta_m)`,
/// `delta_fine := mul delta_m (embed (Rat.natDivSucc 1 n))` — folding
/// `(succ n)` copies of a per-fine-piece constant `w·Δ_fine` back down to
/// `w·Δ_m` exactly, for every `w`. The same four-step
/// `mul_assoc`/`mul_comm`/`mul_assoc`/`mesh_count_width` shape
/// `monotone.rs`'s own Archimedean closing step uses (that file is out of
/// scope for edits, so this reproduces the shape rather than calling it),
/// generalized from a bound-specific `w` to an arbitrary one so
/// [`declare_fine_block_sum_close`] can call it twice — once at `w := F
/// base_i`, once at `w := embed (natDivSucc 1 e)` — instead of duplicating
/// the chain.
fn fold_block_term(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    w: ExprId,
    delta_m: ExprId,
    n: ExprId,
) -> ExprId {
    let one_nat = d.num(1);
    let frac_n_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
    let frac_n = embed(d, p, frac_n_rat);
    let delta_fine = cmul(d, p, delta_m, frac_n);
    let sn = d.succ(n);
    // `sn_real` -- the CReal cast `ofNat (Nat.succ n)`; `sn` itself is a
    // `Nat` and every `mul` below needs its CReal embedding, exactly what
    // `mesh_count_width`'s own `ofNat (Nat.succ m)` is.
    let sn_real = d.const_app(p.of_nat, &[sn]);

    let w_delta_fine = cmul(d, p, w, delta_fine);
    let start = cmul(d, p, sn_real, w_delta_fine); // sn_real * (w * delta_fine)

    let sn_w = cmul(d, p, sn_real, w);
    let s1 = cmul(d, p, sn_w, delta_fine); // (sn_real * w) * delta_fine
    let h1 = {
        let assoc = d.lemma(p.mul_assoc, &[sn_real, w, delta_fine]); // Equiv s1 start
        d.lemma(p.equiv_symm, &[s1, start, assoc])
    };
    // h1 : Equiv start s1

    let w_sn = cmul(d, p, w, sn_real);
    let s2 = cmul(d, p, w_sn, delta_fine); // (w * sn_real) * delta_fine
    let h2 = {
        let comm = d.lemma(p.mul_comm, &[sn_real, w]); // Equiv sn_w w_sn
        let refl_df = d.lemma(p.equiv_refl, &[delta_fine]);
        d.lemma(
            p.mul_congr,
            &[sn_w, w_sn, delta_fine, delta_fine, comm, refl_df],
        )
    };
    // h2 : Equiv s1 s2

    let sn_delta_fine = cmul(d, p, sn_real, delta_fine);
    let s3 = cmul(d, p, w, sn_delta_fine); // w * (sn_real * delta_fine)
    let h3 = d.lemma(p.mul_assoc, &[w, sn_real, delta_fine]); // Equiv s2 s3

    // mesh : Equiv sn_delta_fine delta_m -- `mesh_count_width` at
    // `width := delta_m`, since `delta_fine` IS `mul delta_m frac_n`.
    let mesh = d.lemma(p.mesh_count_width, &[delta_m, n]);
    let target = cmul(d, p, w, delta_m); // w * delta_m
    let h4 = {
        let refl_w = d.lemma(p.equiv_refl, &[w]);
        d.lemma(p.mul_congr, &[w, w, sn_delta_fine, delta_m, refl_w, mesh])
    };
    // h4 : Equiv s3 target

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (target, h4)])
    // : Equiv start target
}

/// `CReal.fineBlockSum_close : ∀ F a b e m n i, le a b → UniformlyContinuousOn
/// F a b → Nat.le i m → Nat.le deep m → And (le blockSum (add coarseTerm
/// epsTerm)) (le coarseTerm (add blockSum epsTerm))`, `deep` the same
/// Archimedean threshold [`declare_fine_sample_close`] uses, and (with
/// `delta_m := mul (width_of a b) (embed (natDivSucc 1 m))`, `base_i :=
/// sample_point a delta_m i`, `delta_fine := mul delta_m (embed (natDivSucc
/// 1 n))`):
///
/// - `blockSum := sumRange (summand_fn F base_i delta_fine) (Nat.succ n)` —
///   the fine Riemann sub-sum over coarse block `i`'s own `Nat.succ n` fine
///   pieces (`summand_fn F base_i delta_fine j = mul (F (sample_point base_i
///   delta_fine j)) delta_fine`, and `sample_point base_i delta_fine j` IS
///   `declare_fine_sample_close`'s own `fine_j`).
/// - `coarseTerm := mul (F base_i) delta_m` — the single term `riemannSum`
///   itself would use at coarse index `i`.
/// - `epsTerm := mul (embed (Rat.natDivSucc 1 e)) delta_m` — the roadmap's
///   own `Δ_m · natDivSucc(1, e)`, commuted.
///
/// Roadmap step 3: bound each coarse block's fine sub-sum between `C(i) ±
/// Δ_m · natDivSucc(1, e)`, the per-block piece `riemannSum_cauchy`'s outer
/// fold (step 4) sums over all `Nat.succ m` blocks.
///
/// Route: per fine index `j < Nat.succ n`, [`declare_fine_sample_close`]
/// gives `close_within (F fine_j) (F base_i) (natDivSucc 1 e)`, and
/// [`declare_two_sided_of_abs_sub_le`] splits it into `le (F fine_j) (add
/// (F base_i) eps)` and `le (F base_i) (add (F fine_j) eps)`. Two
/// applications of `sumRange_le` (upper and lower) lift these, via
/// [`mul_le_mul_of_nonneg_right`] against `delta_fine` and `right_distrib`,
/// to `blockSum` against constant/near-constant sums; `sumRange_const` (and,
/// on the lower side, `sumRange_add`) collapse those, and [`fold_block_term`]
/// (applied twice — once at `w := F base_i`, once at `w := embed
/// (natDivSucc 1 e)`) folds the leftover `(succ n) · delta_fine` factor back
/// down to `delta_m`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_fine_block_sum_close(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let hi_ty = d.le(i, m);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    // deep, EXACTLY as `declare_fine_sample_close` computes it (same
    // Archimedean threshold `mesh_le_of_ge`/`fineSample_close` both use).
    let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let outer = d.apply(modulus_fn, &[e]);
    let width = width_of(d, p, a, b);
    let (c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);
    let me = NatOps::mul(d, magnitude, outer);
    let deep = NatOps::add(d, me, c);
    let hge_ty = d.le(deep, m);
    let hge_fv = d.fresh_fvar();
    let hge = d.kernel().fvar(hge_fv);

    let (delta_m, delta_m_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let base_i = sample_point(d, p, a, delta_m, i);
    let fbase = d.apply(f, &[base_i]);

    let one_nat = d.num(1);
    let frac_n_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
    let frac_n = embed(d, p, frac_n_rat);
    let delta_fine = cmul(d, p, delta_m, frac_n);
    let delta_fine_nonneg = {
        let fnn = frac_nonneg(d, p, n);
        d.lemma(p.mul_nonneg, &[delta_m, frac_n, delta_m_nonneg, fnn])
    };

    let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let eps_embed = embed(d, p, eps_rat);

    let sn = d.succ(n);
    // `sn_real` -- the CReal cast `ofNat (Nat.succ n)`, needed everywhere a
    // count of `Nat.succ n` fine pieces gets multiplied against a `CReal`
    // (see `fold_block_term`'s own note: `sn` itself is a `Nat`).
    let sn_real = d.const_app(p.of_nat, &[sn]);

    // block_summand j = mul (F (sample_point base_i delta_fine j)) delta_fine
    // -- `summand_fn`'s own convention, and `sample_point base_i delta_fine
    // j` IS `declare_fine_sample_close`'s own `fine_j`.
    let block_summand = summand_fn(d, p, f, base_i, delta_fine);
    let block_sum = d.const_app(p.sum_range, &[block_summand, sn]);

    let coarse_term = cmul(d, p, fbase, delta_m);
    let eps_term = cmul(d, p, eps_embed, delta_m);

    // --- upper : le block_sum (add coarse_term eps_term) -------------------
    let upper = {
        let w_upper = cadd(d, p, fbase, eps_embed);
        let per_term = cmul(d, p, w_upper, delta_fine);
        let const_upper_fn = const_nat_fn(d, per_term);

        let pointwise = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hj_ty = d.lt(j, sn);
            let hj_fv = d.fresh_fvar();
            let hj = d.kernel().fvar(hj_fv);

            let hclose = d.const_app(
                p.fine_sample_close,
                &[f, a, b, e, m, n, i, j, hab, u, hi, hj, hge],
            );
            let fine_j = sample_point(d, p, base_i, delta_fine, j);
            let ffine = d.apply(f, &[fine_j]);
            let split = d.const_app(p.two_sided_of_abs_sub_le, &[ffine, fbase, eps_rat, hclose]);
            let fbase_eps = cadd(d, p, fbase, eps_embed);
            let ffine_eps = cadd(d, p, ffine, eps_embed);
            let upper_ty = cle(d, p, ffine, fbase_eps);
            let lower_ty = cle(d, p, fbase, ffine_eps);
            let upper_j = d.const_app(logic.and_left, &[upper_ty, lower_ty, split]);
            // upper_j : le ffine (add fbase eps_embed)

            let grown = mul_le_mul_of_nonneg_right(
                d,
                p,
                ffine,
                w_upper,
                delta_fine,
                delta_fine_nonneg,
                upper_j,
            );
            // grown : le (mul ffine delta_fine) (mul w_upper delta_fine)
            //       = le (block_summand j) per_term

            let applied = d.apply(block_summand, &[j]);
            let refl_applied = d.lemma(p.equiv_refl, &[applied]);
            let ffine_delta = cmul(d, p, ffine, delta_fine);
            let refl_target = d.lemma(p.equiv_refl, &[per_term]);
            let matched = d.lemma(
                p.le_congr,
                &[
                    ffine_delta,
                    applied,
                    per_term,
                    per_term,
                    refl_applied,
                    refl_target,
                    grown,
                ],
            );
            let inner = d.lam_fv(hj_fv, hj_ty, matched);
            d.lam_fv(j_fv, nat, inner)
        };

        let step_upper = d.lemma(
            p.sum_range_le,
            &[block_summand, const_upper_fn, sn, pointwise],
        );
        // step_upper : le block_sum (sumRange const_upper_fn sn)

        let sum_upper_const = d.lemma(p.sum_range_const, &[per_term, n]);
        // sum_upper_const : Equiv (sumRange const_upper_fn sn) (mul sn per_term)

        let sum_upper = d.const_app(p.sum_range, &[const_upper_fn, sn]);
        let sn_per_term = cmul(d, p, sn_real, per_term);
        let refl_block_sum = d.lemma(p.equiv_refl, &[block_sum]);
        let step1 = d.lemma(
            p.le_congr,
            &[
                block_sum,
                block_sum,
                sum_upper,
                sn_per_term,
                refl_block_sum,
                sum_upper_const,
                step_upper,
            ],
        );
        // step1 : le block_sum sn_per_term

        let fold = fold_block_term(d, p, w_upper, delta_m, n);
        // fold : Equiv sn_per_term (mul w_upper delta_m)

        let w_upper_delta_m = cmul(d, p, w_upper, delta_m);
        let step2 = d.lemma(
            p.le_congr,
            &[
                block_sum,
                block_sum,
                sn_per_term,
                w_upper_delta_m,
                refl_block_sum,
                fold,
                step1,
            ],
        );
        // step2 : le block_sum w_upper_delta_m

        let dist = right_distrib(d, p, fbase, eps_embed, delta_m);
        // dist : Equiv w_upper_delta_m (add coarse_term eps_term)
        let target = cadd(d, p, coarse_term, eps_term);
        d.lemma(
            p.le_congr,
            &[
                block_sum,
                block_sum,
                w_upper_delta_m,
                target,
                refl_block_sum,
                dist,
                step2,
            ],
        )
        // : le block_sum target
    };

    // --- lower : le coarse_term (add block_sum eps_term) -------------------
    let lower = {
        let fbase_delta_fine = cmul(d, p, fbase, delta_fine);
        let const_fbase_fn = const_nat_fn(d, fbase_delta_fine);

        let eps_delta_fine = cmul(d, p, eps_embed, delta_fine);
        let const_eps_fn = const_nat_fn(d, eps_delta_fine);

        let rhs_fn = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let fj = d.apply(block_summand, &[j]);
            let gj = d.apply(const_eps_fn, &[j]);
            let body = cadd(d, p, fj, gj);
            d.lam_fv(j_fv, nat, body)
        };

        let pointwise = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hj_ty = d.lt(j, sn);
            let hj_fv = d.fresh_fvar();
            let hj = d.kernel().fvar(hj_fv);

            let hclose = d.const_app(
                p.fine_sample_close,
                &[f, a, b, e, m, n, i, j, hab, u, hi, hj, hge],
            );
            let fine_j = sample_point(d, p, base_i, delta_fine, j);
            let ffine = d.apply(f, &[fine_j]);
            let split = d.const_app(p.two_sided_of_abs_sub_le, &[ffine, fbase, eps_rat, hclose]);
            let fbase_eps = cadd(d, p, fbase, eps_embed);
            let ffine_eps = cadd(d, p, ffine, eps_embed);
            let upper_ty = cle(d, p, ffine, fbase_eps);
            let lower_ty = cle(d, p, fbase, ffine_eps);
            let lower_j = d.const_app(logic.and_right, &[upper_ty, lower_ty, split]);
            // lower_j : le fbase (add ffine eps_embed)

            let w_lower = cadd(d, p, ffine, eps_embed);
            let grown = mul_le_mul_of_nonneg_right(
                d,
                p,
                fbase,
                w_lower,
                delta_fine,
                delta_fine_nonneg,
                lower_j,
            );
            // grown : le fbase_delta_fine (mul w_lower delta_fine)

            let dist = right_distrib(d, p, ffine, eps_embed, delta_fine);
            // dist : Equiv (mul w_lower delta_fine) (add (mul ffine delta_fine)
            //   (mul eps_embed delta_fine)) = Equiv (...) (rhs_fn j)
            let refl_lhs = d.lemma(p.equiv_refl, &[fbase_delta_fine]);
            let w_lower_delta_fine = cmul(d, p, w_lower, delta_fine);
            let rhs_at_j = d.apply(rhs_fn, &[j]);
            let matched = d.lemma(
                p.le_congr,
                &[
                    fbase_delta_fine,
                    fbase_delta_fine,
                    w_lower_delta_fine,
                    rhs_at_j,
                    refl_lhs,
                    dist,
                    grown,
                ],
            );
            let inner = d.lam_fv(hj_fv, hj_ty, matched);
            d.lam_fv(j_fv, nat, inner)
        };

        let step_lower = d.lemma(p.sum_range_le, &[const_fbase_fn, rhs_fn, sn, pointwise]);
        // step_lower : le (sumRange const_fbase_fn sn) (sumRange rhs_fn sn)

        // LHS: sumRange const_fbase_fn sn ~ mul sn fbase_delta_fine ~ coarse_term.
        let lhs_const = d.lemma(p.sum_range_const, &[fbase_delta_fine, n]);
        let sn_fbase_delta_fine = cmul(d, p, sn_real, fbase_delta_fine);
        let lhs_fold = fold_block_term(d, p, fbase, delta_m, n);
        let sum_fbase = d.const_app(p.sum_range, &[const_fbase_fn, sn]);
        let lhs_chain = echain(
            d,
            p,
            sum_fbase,
            &[(sn_fbase_delta_fine, lhs_const), (coarse_term, lhs_fold)],
        );
        // lhs_chain : Equiv sum_fbase coarse_term

        // RHS: sumRange rhs_fn sn ~ add block_sum (sumRange const_eps_fn sn)
        //   ~ add block_sum eps_term.
        let sum_add = d.lemma(p.sum_range_add, &[block_summand, const_eps_fn, sn]);
        // sum_add : Equiv (sumRange rhs_fn sn) (add block_sum (sumRange
        //   const_eps_fn sn))  -- since `rhs_fn` IS `fun j => add
        //   (block_summand j) (const_eps_fn j)`.
        let sum_eps = d.const_app(p.sum_range, &[const_eps_fn, sn]);
        let add_block_sum_eps = cadd(d, p, block_sum, sum_eps);

        let eps_const = d.lemma(p.sum_range_const, &[eps_delta_fine, n]);
        let sn_eps_delta_fine = cmul(d, p, sn_real, eps_delta_fine);
        let eps_fold = fold_block_term(d, p, eps_embed, delta_m, n);
        let eps_chain = echain(
            d,
            p,
            sum_eps,
            &[(sn_eps_delta_fine, eps_const), (eps_term, eps_fold)],
        );
        // eps_chain : Equiv sum_eps eps_term

        let refl_block_sum = d.lemma(p.equiv_refl, &[block_sum]);
        let target = cadd(d, p, block_sum, eps_term);
        let sum_rhs_fn = d.const_app(p.sum_range, &[rhs_fn, sn]);
        let rhs_chain = {
            let step = d.lemma(
                p.add_congr,
                &[
                    block_sum,
                    block_sum,
                    sum_eps,
                    eps_term,
                    refl_block_sum,
                    eps_chain,
                ],
            );
            // step : Equiv add_block_sum_eps target
            echain(
                d,
                p,
                sum_rhs_fn,
                &[(add_block_sum_eps, sum_add), (target, step)],
            )
        };
        // rhs_chain : Equiv (sumRange rhs_fn sn) target

        d.lemma(
            p.le_congr,
            &[
                sum_fbase,
                coarse_term,
                sum_rhs_fn,
                target,
                lhs_chain,
                rhs_chain,
                step_lower,
            ],
        )
        // : le coarse_term target
    };

    let coarse_plus_eps = cadd(d, p, coarse_term, eps_term);
    let block_sum_plus_eps = cadd(d, p, block_sum, eps_term);
    let upper_ty = cle(d, p, block_sum, coarse_plus_eps);
    let lower_ty = cle(d, p, coarse_term, block_sum_plus_eps);
    let conclusion_proof = and_intro(d, p, upper_ty, lower_ty, upper, lower);

    let ty = {
        let and_ty = d.const_app(logic.and, &[upper_ty, lower_ty]);
        let after_hge = d.arrow(hge_ty, and_ty);
        let after_hi = d.arrow(hi_ty, after_hge);
        let after_u = d.pi_fv(u_fv, u_ty, after_hi);
        let after_hab = d.arrow(hab_ty, after_u);
        let over_i = d.pi_fv(i_fv, nat, after_hab);
        let over_n = d.pi_fv(n_fv, nat, over_i);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_e = d.pi_fv(e_fv, nat, over_m);
        let over_b = d.pi_fv(b_fv, carrier, over_e);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_hge = d.lam_fv(hge_fv, hge_ty, conclusion_proof);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hge);
        let with_u = d.lam_fv(u_fv, u_ty, with_hi);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_i = d.lam_fv(i_fv, nat, with_hab);
        let over_n = d.lam_fv(n_fv, nat, over_i);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_e = d.lam_fv(e_fv, nat, over_m);
        let over_b = d.lam_fv(b_fv, carrier, over_e);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.fine_block_sum_close,
        uparams: vec![],
        ty,
        value,
    })
}

fn double_block(d: &mut IntDev<'_>, p: CRealPrelude, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let two = d.num(2);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let two_i = NatOps::mul(d, two, i);
    let g0 = d.apply(g, &[two_i]);
    let s2i = d.succ(two_i);
    let g1 = d.apply(g, &[s2i]);
    let body = cadd(d, p, g0, g1);
    d.lam_fv(i_fv, nat, body)
}

/// `Equiv (sumRange g (Nat.mul 2 k)) (sumRange (double_block g) k)` — the
/// proof term, by induction on `k`.
///
/// `Nat.mul`/`Nat.add` are both `define_binary`, recursing on their SECOND
/// argument, and the literal `2` (`d.num(2)`) is a genuine `succ (succ
/// zero)` term (`NatOps::num`'s own definition, not an opaque numeral), so
/// `Nat.mul 2 (Nat.succ j)` reduces by pure defeq (delta+iota, no lemma) to
/// `Nat.succ (Nat.succ (Nat.mul 2 j))` — unfold `mul` once on `succ j`
/// (`define_binary`'s step equation) to `Nat.add (Nat.mul 2 j) 2`, then
/// unfold `add` twice on the literal `2`'s own two `succ`s. `sumRange`'s own
/// recursion then unfolds `sumRange g (succ (succ (mul 2 j)))` twice against
/// that same shape, so the only PROOF content needed is one `add_congr`
/// (lifting the induction hypothesis one `add` level in) and one
/// `add_assoc` (re-bracketing the trailing pair together) — no rewriting of
/// the `Nat` indices themselves.
fn sum_range_double_proof(d: &mut IntDev<'_>, p: CRealPrelude, g: ExprId, k: ExprId) -> ExprId {
    let grouped = double_block(d, p, g);
    let two = d.num(2);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let two_x = NatOps::mul(d, two, x);
        let lhs = d.const_app(p.sum_range, &[g, two_x]);
        let rhs = d.const_app(p.sum_range, &[grouped, x]);
        equiv(d, p, lhs, rhs)
    };

    d.induct(
        &motive,
        &|d| {
            // motive(zero): both sides reduce (defeq) to `CReal.zero`.
            let zero_c = czero(d, p);
            d.lemma(p.equiv_refl, &[zero_c])
        },
        &|d, j, ih| {
            // ih : Equiv (sumRange g (mul 2 j)) (sumRange grouped j)
            // Goal (defeq unfolded): Equiv
            //   (add (add (sumRange g (mul 2 j)) (g (mul 2 j))) (g (succ (mul 2 j))))
            //   (add (sumRange grouped j) (add (g (mul 2 j)) (g (succ (mul 2 j)))))
            let two_j = NatOps::mul(d, two, j);
            let gj = d.apply(g, &[two_j]);
            let s2j = d.succ(two_j);
            let gj1 = d.apply(g, &[s2j]);

            let sum_g_2j = d.const_app(p.sum_range, &[g, two_j]);
            let sum_grouped_j = d.const_app(p.sum_range, &[grouped, j]);

            // h1 : Equiv (add sum_g_2j gj) (add sum_grouped_j gj)
            let refl_gj = d.lemma(p.equiv_refl, &[gj]);
            let h1 = d.lemma(p.add_congr, &[sum_g_2j, sum_grouped_j, gj, gj, ih, refl_gj]);

            // h2 : Equiv (add (add sum_g_2j gj) gj1) (add (add sum_grouped_j gj) gj1)
            let lhs1 = cadd(d, p, sum_g_2j, gj);
            let rhs1 = cadd(d, p, sum_grouped_j, gj);
            let refl_gj1 = d.lemma(p.equiv_refl, &[gj1]);
            let h2 = d.lemma(p.add_congr, &[lhs1, rhs1, gj1, gj1, h1, refl_gj1]);

            // h3 : Equiv (add (add sum_grouped_j gj) gj1) (add sum_grouped_j (add gj gj1))
            let h3 = d.lemma(p.add_assoc, &[sum_grouped_j, gj, gj1]);

            let start = cadd(d, p, lhs1, gj1);
            let lhs2 = cadd(d, p, rhs1, gj1);
            let rhs2 = {
                let inner = cadd(d, p, gj, gj1);
                cadd(d, p, sum_grouped_j, inner)
            };
            d.lemma(p.equiv_trans, &[start, lhs2, rhs2, h2, h3])
        },
        k,
    )
}

/// `CReal.sumRange_double : ∀ g k, Equiv (sumRange g (Nat.mul 2 k))
/// (sumRange (fun i => add (g (Nat.mul 2 i)) (g (Nat.succ (Nat.mul 2 i))))
/// k)`. See this section's own module documentation for what this is for
/// and precisely what is not yet built on top of it.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_sum_range_double(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let proof = sum_range_double_proof(d, p, g, k);

    let ty = {
        let two = d.num(2);
        let two_k = NatOps::mul(d, two, k);
        let lhs = d.const_app(p.sum_range, &[g, two_k]);
        let grouped = double_block(d, p, g);
        let rhs = d.const_app(p.sum_range, &[grouped, k]);
        equiv(d, p, lhs, rhs)
    };
    let ty_full = {
        let over_k = d.pi_fv(k_fv, nat, ty);
        d.pi_fv(g_fv, fn_ty, over_k)
    };
    let value_full = {
        let over_k = d.lam_fv(k_fv, nat, proof);
        d.lam_fv(g_fv, fn_ty, over_k)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_double,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

// --- `CReal.ofNat_add` / `CReal.ofNat_mul` -- toward `riemannSum_cauchy` ---
//
// `CReal.sumRange_reblock`'s conclusion indexes the fine sum at the RAW
// global index `(succ n)*i + j`; comparing a coarse `riemannSum` block's
// single term against that block's `succ n` fine terms needs the LOCAL
// sample-point arithmetic `a + i*delta_m + j*delta_fine` instead (`delta_fine
// := delta_m * natDivSucc 1 n`, chosen so `(succ n)*delta_fine ~ delta_m` is
// exactly `CReal.mesh_count_width` at `(delta_m, n)` -- no new identity
// needed there). Bridging the two needs `CReal.ofNat` to commute with
// `Nat.add`/`Nat.mul`, which no existing lemma states. Both are direct, with
// no induction on either argument: `CReal.ofNat n := CReal.ofRat
// (Rat.natDivSucc n 0)`, so lifting `Rat.natDivSucc`'s own homomorphism facts
// at denominator index `0` (`RatPrelude::nat_div_succ_add`/`nat_div_succ_mul`,
// the latter already general in its SECOND denominator index, so `0` is just
// one instance) across `CReal.ofRat` via `CReal.ofRat_add`/`CReal.ofRat_mul`
// closes each in one step -- the same one-step-lift idiom
// [`nat_div_succ_inverse_pair_eq_one`] already uses `nat_div_succ_mul` for,
// above.

/// `CReal.ofNat_add : ∀ a b : Nat, Equiv (ofNat (Nat.add a b)) (add (ofNat a)
/// (ofNat b))`. See this section's own module documentation.
fn declare_of_nat_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let rat = p.rat;

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let zero_nat = d.num(0);
    let rat_a = d.const_app(rat.nat_div_succ, &[a, zero_nat]);
    let rat_b = d.const_app(rat.nat_div_succ, &[b, zero_nat]);
    let of_nat_a = embed(d, p, rat_a); // defeq (ofNat a)
    let of_nat_b = embed(d, p, rat_b); // defeq (ofNat b)
    let sum_real = cadd(d, p, of_nat_a, of_nat_b);
    // The nicer, `CReal.ofNat`-headed form of `sum_real`, defeq to it (one
    // delta step each side), used only for the OUTWARD-facing `ty`/`value` so
    // the declared statement and its rendered type read `ofNat a`/`ofNat b`
    // rather than the unfolded `ofRat (natDivSucc a 0)` the internal rewrite
    // chain below works with.
    let of_nat_a_nice = d.const_app(p.of_nat, &[a]);
    let of_nat_b_nice = d.const_app(p.of_nat, &[b]);
    let sum_real_nice = cadd(d, p, of_nat_a_nice, of_nat_b_nice);

    // step1 : Equiv sum_real (ofRat (Rat.add rat_a rat_b))
    let step1 = d.lemma(p.of_rat_add, &[rat_a, rat_b]);

    let sum_rat = radd(d, rat_a, rat_b);
    let nat_sum = NatOps::add(d, a, b);
    let rat_target = d.const_app(rat.nat_div_succ, &[nat_sum, zero_nat]);
    // add_eq : Eq Rat sum_rat rat_target
    let add_eq = d.lemma(rat.nat_div_succ_add, &[a, b, zero_nat]);

    let rewritten = rat_eq_rewrite(d, sum_rat, rat_target, add_eq, step1, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, sum_real, embedded)
    });
    // rewritten : Equiv sum_real (embed rat_target) -- defeq
    // Equiv sum_real_nice (ofNat nat_sum), since `sum_real ~defeq~ sum_real_nice`
    // and `embed rat_target ~defeq~ ofNat nat_sum`.
    let of_nat_sum = d.const_app(p.of_nat, &[nat_sum]);
    let flipped = d.lemma(p.equiv_symm, &[sum_real_nice, of_nat_sum, rewritten]);
    // flipped : Equiv of_nat_sum sum_real_nice

    let ty = {
        let concl = equiv(d, p, of_nat_sum, sum_real_nice);
        let over_b = d.pi_fv(b_fv, nat, concl);
        d.pi_fv(a_fv, nat, over_b)
    };
    let value = {
        let over_b = d.lam_fv(b_fv, nat, flipped);
        d.lam_fv(a_fv, nat, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_nat_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.ofNat_mul : ∀ a b : Nat, Equiv (ofNat (Nat.mul a b)) (mul (ofNat a)
/// (ofNat b))`. See this section's own module documentation.
fn declare_of_nat_mul(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let rat = p.rat;

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let zero_nat = d.num(0);
    let rat_a = d.const_app(rat.nat_div_succ, &[a, zero_nat]);
    let rat_b = d.const_app(rat.nat_div_succ, &[b, zero_nat]);
    let of_nat_a = embed(d, p, rat_a);
    let of_nat_b = embed(d, p, rat_b);
    let prod_real = cmul(d, p, of_nat_a, of_nat_b);
    // The nicer, `CReal.ofNat`-headed form, defeq to `prod_real` -- see
    // `declare_of_nat_add`'s identical comment above.
    let of_nat_a_nice = d.const_app(p.of_nat, &[a]);
    let of_nat_b_nice = d.const_app(p.of_nat, &[b]);
    let prod_real_nice = cmul(d, p, of_nat_a_nice, of_nat_b_nice);

    // step1 : Equiv prod_real (ofRat (Rat.mul rat_a rat_b))
    let step1 = d.lemma(p.of_rat_mul, &[rat_a, rat_b]);

    let prod_rat = rmul(d, rat_a, rat_b);
    let nat_prod = NatOps::mul(d, a, b);
    let rat_target = d.const_app(rat.nat_div_succ, &[nat_prod, zero_nat]);
    // mul_eq : Eq Rat prod_rat rat_target
    let mul_eq = d.lemma(rat.nat_div_succ_mul, &[a, b, zero_nat]);

    let rewritten = rat_eq_rewrite(d, prod_rat, rat_target, mul_eq, step1, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, prod_real, embedded)
    });
    let of_nat_prod = d.const_app(p.of_nat, &[nat_prod]);
    let flipped = d.lemma(p.equiv_symm, &[prod_real_nice, of_nat_prod, rewritten]);

    let ty = {
        let concl = equiv(d, p, of_nat_prod, prod_real_nice);
        let over_b = d.pi_fv(b_fv, nat, concl);
        d.pi_fv(a_fv, nat, over_b)
    };
    let value = {
        let over_b = d.lam_fv(b_fv, nat, flipped);
        d.lam_fv(a_fv, nat, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_nat_mul,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.ofNat_add` and `CReal.ofNat_mul`. See this section's own
/// module documentation for what they bridge toward `riemannSum_cauchy`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_of_nat_hom(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_of_nat_add(d, p)?;
    declare_of_nat_mul(d, p)
}

// --- the succ-shape bridge -- toward `riemannSum_cauchy`'s common refinement
//
// The refinement estimate `riemannSum_cauchy` needs bounds each fine sample
// point against its enclosing coarse sample via
// `CReal.UniformlyContinuousOn.spec`, and the domain-membership hypotheses
// that call needs (`a≤x, x≤b, a≤y, y≤b`) come from `riemannSum_sample_in_bounds`
// / `subdivisionPoint_in_bounds` -- both stated for a partition of a
// `Nat.succ`-shaped count (`Nat.lt i (Nat.succ m)` / `Nat.le i (Nat.succ m)`).
// The fine partition (each of the coarse partition's `Nat.succ n` pieces
// split into `Nat.succ m` further pieces) has total count `(Nat.succ
// n)·(Nat.succ m)`, which every fine index genuinely satisfies but not
// SYNTACTICALLY as `Nat.succ` of anything -- so calling either theorem there
// needs a bridge exhibiting the count in `Nat.succ _` shape.
//
// The needed identity is `(succ n)·(succ m) = succ (n·m + n + m)`,
// `m_prime := n·m + n + m`. [`succ_mul_succ`] below returns it in COMPUTED
// form (`m_prime : Nat` plus a proof), not as an `∃ m', succ m' = …`: both
// `riemannSum_sample_in_bounds` and `subdivisionPoint_in_bounds` take the
// subdivision count as a plain `Nat` DATA argument, used to build the CReal
// sample-point term itself (a `Type`-valued position), and `Exists.rec`
// eliminates only into `Prop` -- an existential witness could not be
// substituted there at all, only used inside an already-Prop-valued goal.
// This is exactly the trap this session's own briefing warned about: "a
// theorem admitted with a type nothing can use."

/// `(Nat.succ n) · (Nat.succ m) = Nat.succ ((n·m + n) + m)` — the succ-shape
/// bridge above, as a private proof-term builder (not a public
/// `CRealPrelude` declaration: this is pure `Nat` arithmetic, out of this
/// file's natural home, but per this session's scope constraints it is
/// landed here rather than in the shared `nat_prelude` — relocate on
/// request).
///
/// Proof: `Nat.succ_mul n (Nat.succ m) : Eq Nat (mul (succ n) (succ m)) (add
/// (mul n (succ m)) (succ m))`. `Nat.mul`/`Nat.add` both recurse on their
/// RIGHT argument (`Nat.mul_succ`/`Nat.add_succ` are `refl`, not induction),
/// so with `sm := succ m` already `succ`-shaped, `mul n sm` unfolds by pure
/// defeq to `add (mul n m) n`, and then `add (add (mul n m) n) sm` unfolds
/// by pure defeq to `succ (add (add (mul n m) n) m)` — i.e. `succ m_prime`.
/// So `Nat.succ_mul`'s own proof term, with NO further rewrite or congruence
/// step, already has the stronger stated type up to the kernel's conversion
/// check; this returns that proof term unchanged.
///
/// Returns `(m_prime, proof)`, `proof : Eq Nat (mul (succ n) (succ m)) (succ
/// m_prime)`, `m_prime := add (add (mul n m) n) m`.
fn succ_mul_succ(d: &mut IntDev<'_>, n: ExprId, m: ExprId) -> (ExprId, ExprId) {
    let np = d.prelude();
    let sm = d.succ(m);
    let nm = NatOps::mul(d, n, m);
    let nm_n = d.const_app(np.add, &[nm, n]);
    let m_prime = d.const_app(np.add, &[nm_n, m]);
    let proof = d.lemma(np.succ_mul, &[n, sm]);
    (m_prime, proof)
}

/// `CReal.meshReciprocalMul : ∀ n m : Nat,
/// Eq Rat (Rat.mul (Rat.natDivSucc 1 n) (Rat.natDivSucc 1 m))
///        (Rat.natDivSucc 1 (Nat.add (Nat.add (Nat.mul n m) n) m))` —
/// refining a partition of `succ m` coarse pieces into `succ n` further
/// pieces each gives a fine mesh factor `1/(n+1) · 1/(m+1)` EXACTLY equal
/// (not merely close) to the single-partition factor `1/(m_prime+1)`,
/// `m_prime := ((n·m)+n)+m` — [`succ_mul_succ`]'s own witness, chosen
/// exactly so `Nat.succ m_prime` is definitionally `(Nat.succ n)·(Nat.succ
/// m)`. The reciprocal-mesh multiplicativity `riemannSum_cauchy`'s common
/// refinement needs, toward reconciling `sumRange_reblock`'s RAW global fine
/// index against `riemannSum`'s own per-block sample-point arithmetic (see
/// this module's own documentation).
///
/// Route: `Rat.natDivSucc k j := normalize (ofNat k) (succ j) _`
/// definitionally, so `Rat.mul (natDivSucc 1 n) (natDivSucc 1 m)` unfolds to
/// `normalize (ofNat 1) (succ n) _ · normalize (ofNat 1) (succ m) _`, and
/// [`RatPrelude::normalize_mul_normalize`] gives this equal to `normalize
/// (Int.mul (ofNat 1) (ofNat 1)) (Nat.mul (succ n) (succ m)) _`.
///
/// **`Nat.mul (succ n) (succ m)` does NOT ι-reduce to `succ m_prime` on its
/// own, and a first version of this declaration assumed it did.** `Nat.mul`
/// recurses on its RIGHT argument, so `mul (succ n) (succ m)` unfolds (right
/// argument `succ m` is succ-shaped) to `add (mul (succ n) m) (succ n)` —
/// STUCK at `mul (succ n) m`, a mul with `succ n` (not `n`) on the left,
/// which cannot reduce further since ITS right argument `m` is symbolic.
/// `Nat.succ_mul`, which [`succ_mul_succ`] actually calls, avoids this by
/// peeling the `succ` off the LEFT via an explicit induction-proved theorem
/// FIRST (`mul (succ n) sm = add (mul n sm) sm`, `sm := succ m`), and only
/// the resulting `add (mul n sm) sm` — with `n` (not `succ n`) inside the
/// inner `mul` — unfolds the rest of the way to `succ m_prime` by pure
/// defeq. So `Nat.mul (succ n) (succ m)` and `succ m_prime` are
/// PROPOSITIONALLY equal (via [`succ_mul_succ`]'s own witness, valid at
/// that stronger type for the same reason its own smoke tests confirm) but
/// NOT definitionally equal, and the two must be bridged by an explicit
/// rewrite: `Int.mul (ofNat 1) (ofNat 1)` ι-reduces to `ofNat 1` on its own
/// (both factors are the CONCRETE literal `1`, so `Nat.mul 1 1` fully
/// computes with no symbolic subterm — this half needs no bridge), lifted
/// to `Eq Int` via [`IntDev::nat_eq_to_int`] multiplying through by
/// `ofNat 1`, and [`RatPrelude::normalize_congr`] (cross-multiplication
/// based, so it needs no defeq between the two denominators at all) closes
/// the gap between `normalize (Int.mul (ofNat 1) (ofNat 1)) (Nat.mul (succ
/// n) (succ m)) _` and the declared `natDivSucc 1 m_prime`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_reciprocal_mul(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let one_nat = d.num(1);
    let n1 = d.of_nat(one_nat);
    let sn = d.succ(n);
    let sm = d.succ(m);
    let h1 = one_le_succ(d, n);
    let h2 = one_le_succ(d, m);

    let proof = d.lemma(p.rat.normalize_mul_normalize, &[n1, sn, h1, n1, sm, h2]);
    // proof : Eq Rat (natDivSucc 1 n * natDivSucc 1 m)
    //                (normalize (Int.mul n1 n1) (Nat.mul sn sm) pos1)

    let (m_prime, succ_proof) = succ_mul_succ(d, n, m);
    let sm_prime = d.succ(m_prime);

    // `mul_sn_sm` MUST be built the same way `normalize_mul_normalize`'s own
    // conclusion computes its denominator (`NatOps::mul(e1, e2)`), so it is
    // syntactically the SAME term `proof`'s actual type already mentions,
    // not merely an equal one.
    let mul_sn_sm = NatOps::mul(d, sn, sm);

    // `succ_proof`'s ACTUAL type is `Eq Nat (mul sn sm) (add (add (mul n m)
    // n) m)`; its RHS reduces by pure defeq to `Nat.succ m_prime` (`Nat.add`
    // unfolding once on its own succ-shaped right argument) -- see
    // `succ_mul_succ`'s doc and this declaration's own doc for why the LHS
    // needs no reduction at all (same literal term). So `succ_proof` is
    // directly usable at the stronger type `Eq Nat mul_sn_sm sm_prime`.
    let nat_bridge = succ_proof;

    // step : Eq Int (n1 * ofNat mul_sn_sm) (n1 * ofNat sm_prime), lifting
    // `nat_bridge` to `Int` by multiplying both sides by `n1`.
    let step = d.nat_eq_to_int(mul_sn_sm, sm_prime, nat_bridge, &|d, t| {
        let ot = d.of_nat(t);
        d.imul(n1, ot)
    });
    let of_mul_sn_sm = d.of_nat(mul_sn_sm);
    let of_sm_prime = d.of_nat(sm_prime);
    let lhs_int = d.imul(n1, of_mul_sn_sm);
    let rhs_int = d.imul(n1, of_sm_prime);
    // cross_eq : Eq Int (n1 * ofNat sm_prime) (n1 * ofNat mul_sn_sm) --
    // `normalize_congr`'s own cross-multiplication shape at
    // (n1' := Int.mul n1 n1, d1' := mul_sn_sm, n2' := n1, d2' := sm_prime),
    // since `Int.mul n1 n1` is DEFEQ `n1` (both factors the concrete literal
    // `ofNat 1`, so `Nat.mul 1 1` fully computes -- unlike `Nat.mul sn sm`,
    // symbolic in `n, m`).
    let cross_eq = d.isymm(lhs_int, rhs_int, step);

    let pos1 = d.lemma(p.rat.int.nat.one_le_mul, &[sn, sm, h1, h2]);
    let pos2 = one_le_succ(d, m_prime);
    let n1_n1 = d.imul(n1, n1);

    let bridge = d.lemma(
        p.rat.normalize_congr,
        &[n1_n1, mul_sn_sm, pos1, n1, sm_prime, pos2, cross_eq],
    );
    // bridge : Eq Rat (normalize n1_n1 mul_sn_sm pos1) (normalize n1 sm_prime pos2)

    let dn = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
    let dm = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let lhs_nice = rmul(d, dn, dm);
    let mid = normalize(d, n1_n1, mul_sn_sm, pos1);
    let rhs_nice = d.const_app(p.rat.nat_div_succ, &[one_nat, m_prime]);

    let full_proof = rtrans(d, lhs_nice, mid, rhs_nice, proof, bridge);
    let stmt = req(d, lhs_nice, rhs_nice);

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        d.pi_fv(n_fv, nat, over_m)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, full_proof);
        d.lam_fv(n_fv, nat, over_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_reciprocal_mul,
        uparams: vec![],
        ty,
        value,
    })
}

// --- roadmap step 1: bridging the global fine index to the local block
// sample point ---------------------------------------------------------
//
// `CReal.sumRange_reblock` sums an arbitrary `g` at the RAW global index
// `(succ n)*i + j`; `CReal.fineBlockSum_close` (roadmap step 3) folds a sum
// over the LOCAL fine index `j`, sampled off the coarse block's own point
// `base_i`. Gluing the two needs `F` applied to two sample points that are
// only `Equiv`, not syntactically equal (this file's own module
// documentation flags exactly this gap). This section proves that bridge as
// an UNCONDITIONAL identity -- no bound on `i`/`j` needed at all, unlike
// every other roadmap step, which all need `i ≤ m`/`j < Nat.succ n` to place
// a sample point in `[a, b]`: the two points denote the same real number
// regardless of which fine sub-index or which coarse block, purely from
// `ofNat_add`/`ofNat_mul` distributing the index arithmetic and
// `mesh_count_width` cancelling the `Nat.succ n` factor `meshReciprocalMul`
// introduces.

/// `Equiv delta_m_prime delta_fine`. `delta_m_prime := mul width (embed
/// (Rat.natDivSucc 1 m_prime))` is the mesh at the REFINED count `Nat.succ
/// m_prime`; `delta_fine := mul (mul width (embed (Rat.natDivSucc 1 m)))
/// (embed (Rat.natDivSucc 1 n))` is the coarse mesh `width *
/// natDivSucc(1,m)` split into `Nat.succ n` further pieces -- the EXACT (not
/// merely close) mesh identity `CReal.meshReciprocalMul`
/// gives at the rational level, lifted to `CReal` by `CReal.ofRat_mul` and
/// reassociated to `delta_fine`'s own bracketing. `m_prime` is not
/// constrained here to equal `((n·m)+n)+m` syntactically -- the caller
/// supplies whatever `m_prime` [`succ_mul_succ`] returned, matching
/// `CReal.meshReciprocalMul`'s own conclusion at that same witness.
///
/// Route: `Rat.mul_comm` turns `meshReciprocalMul`'s own `natDivSucc 1 n *
/// natDivSucc 1 m` into the order `delta_fine`'s bracketing needs
/// (`natDivSucc 1 m * natDivSucc 1 n`) via one `Eq Rat` transitivity step;
/// `rat_eq_rewrite` then rewrites a `CReal.Equiv` built from
/// `CReal.ofRat_mul` (turning `embed (mul frac_m frac_n)` into `mul (embed
/// frac_m) (embed frac_n)`) and `mul_assoc` (re-bracketing `width *
/// (frac_m * frac_n)` to `(width * frac_m) * frac_n`, i.e. `delta_m *
/// frac_n`) along that identity.
fn mesh_reblock_delta_eq(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    width: ExprId,
    n: ExprId,
    m: ExprId,
    m_prime: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let one_nat = d.num(1);
    let frac_m = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_n = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
    let frac_m_prime = d.const_app(p.rat.nat_div_succ, &[one_nat, m_prime]);
    let embed_frac_m = embed(d, p, frac_m);
    let embed_frac_n = embed(d, p, frac_n);
    let delta_m = cmul(d, p, width, embed_frac_m);
    let delta_fine = cmul(d, p, delta_m, embed_frac_n);
    let embed_frac_m_prime = embed(d, p, frac_m_prime);
    let delta_m_prime = cmul(d, p, width, embed_frac_m_prime);

    // h_comm : Eq Rat (mul frac_m frac_n) (mul frac_n frac_m)
    let h_comm = d.lemma(p.rat.mul_comm, &[frac_m, frac_n]);
    // h_recip : Eq Rat (mul frac_n frac_m) frac_m_prime
    let h_recip = d.lemma(p.mesh_reciprocal_mul, &[n, m]);
    let mul_fm_fn = rmul(d, frac_m, frac_n);
    let mul_fn_fm = rmul(d, frac_n, frac_m);
    // h_recip_prime : Eq Rat (mul frac_m frac_n) frac_m_prime
    let h_recip_prime = rtrans(d, mul_fm_fn, mul_fn_fm, frac_m_prime, h_comm, h_recip);

    // pre : Equiv (mul width (embed (mul frac_m frac_n))) delta_fine
    let pre = {
        let embed_prod = embed(d, p, mul_fm_fn);
        let mid_inner = cmul(d, p, embed_frac_m, embed_frac_n);
        // of_rat_mul_step : Equiv mid_inner embed_prod
        let of_rat_mul_step = d.lemma(p.of_rat_mul, &[frac_m, frac_n]);
        // step1 : Equiv embed_prod mid_inner
        let step1 = d.lemma(p.equiv_symm, &[mid_inner, embed_prod, of_rat_mul_step]);
        let refl_width = d.lemma(p.equiv_refl, &[width]);
        let mid = cmul(d, p, width, mid_inner);
        let lhs = cmul(d, p, width, embed_prod);
        // h_a : Equiv lhs mid
        let h_a = d.lemma(
            p.mul_congr,
            &[width, width, embed_prod, mid_inner, refl_width, step1],
        );
        // assoc : Equiv delta_fine mid
        let assoc = d.lemma(p.mul_assoc, &[width, embed_frac_m, embed_frac_n]);
        // h_b : Equiv mid delta_fine
        let h_b = d.lemma(p.equiv_symm, &[delta_fine, mid, assoc]);
        echain(d, p, lhs, &[(mid, h_a), (delta_fine, h_b)])
    };

    let motive = |d: &mut IntDev<'_>, t: ExprId| -> ExprId {
        let embedded = embed(d, p, t);
        let lhs = cmul(d, p, width, embedded);
        equiv(d, p, lhs, delta_fine)
    };
    // proof : Equiv delta_m_prime delta_fine
    let proof = rat_eq_rewrite(d, mul_fm_fn, frac_m_prime, h_recip_prime, pre, &motive);
    (delta_m_prime, delta_fine, proof)
}

/// `(lhs, rhs, proof)` for `CReal.samplePoint_reblock` at `a, b, n, m, i, j`
/// -- see [`declare_sample_point_reblock`]'s own doc comment for the full
/// statement. Built entirely from EXPLICIT congruence/associativity/
/// commutativity steps (never relying on the two sides merely being
/// defeq-shaped alike): every reassociation the derivation needs
/// (`mul_assoc`/`mul_comm` moving the `Nat.succ n` factor across, `add_assoc`
/// re-bracketing the two summands) is its own named lemma application, so
/// this builds identically whether `a, b, n, m, i, j` are free variables (as
/// [`declare_sample_point_reblock`] itself uses) or ground literals (as the
/// concrete instantiation test below uses) -- the exact distinction the
/// session's own caution about symbolic-vs-concrete defects warns is not
/// automatic.
fn sample_point_reblock_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    m: ExprId,
    i: ExprId,
    j: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let width = width_of(d, p, a, b);
    let (m_prime, _succ_proof) = succ_mul_succ(d, n, m);
    let (delta_m_prime, delta_fine, delta_eq) = mesh_reblock_delta_eq(d, p, width, n, m, m_prime);
    let delta_m = delta_of(d, p, a, b, m);
    let base_i = sample_point(d, p, a, delta_m, i);

    let sn = d.succ(n);
    let sn_i = NatOps::mul(d, sn, i);
    let global_idx = NatOps::add(d, sn_i, j);

    let of_nat_sn = d.const_app(p.of_nat, &[sn]);
    let of_nat_i = d.const_app(p.of_nat, &[i]);
    let of_nat_j = d.const_app(p.of_nat, &[j]);
    let of_nat_sn_i = d.const_app(p.of_nat, &[sn_i]);
    let of_nat_global = d.const_app(p.of_nat, &[global_idx]);

    let lhs = sample_point(d, p, a, delta_m_prime, global_idx);
    let rhs = sample_point(d, p, base_i, delta_fine, j);

    let mul_sn_i_term = cmul(d, p, of_nat_sn, of_nat_i);
    let ofnat_split = cadd(d, p, mul_sn_i_term, of_nat_j);
    let term_i_part = cmul(d, p, mul_sn_i_term, delta_m_prime);
    let term_j_part = cmul(d, p, of_nat_j, delta_m_prime);
    let sum_parts = cadd(d, p, term_i_part, term_j_part);
    let mul_i_dm = cmul(d, p, of_nat_i, delta_m);
    let mul_j_fine = cmul(d, p, of_nat_j, delta_fine);
    let target_sum = cadd(d, p, mul_i_dm, mul_j_fine);
    let mul_global_dmp = cmul(d, p, of_nat_global, delta_m_prime);
    let mul_split_dmp = cmul(d, p, ofnat_split, delta_m_prime);
    let a_mul_split_dmp = cadd(d, p, a, mul_split_dmp);
    let a_sum_parts = cadd(d, p, a, sum_parts);
    let a_target_sum = cadd(d, p, a, target_sum);

    // Step A : Equiv of_nat_global ofnat_split -- `ofNat_add`/`ofNat_mul`
    // splitting the global index into its block/offset shape.
    let h_ofnat_global = {
        let mid = cadd(d, p, of_nat_sn_i, of_nat_j);
        let step1 = d.lemma(p.of_nat_add, &[sn_i, j]);
        let step2 = d.lemma(p.of_nat_mul, &[sn, i]);
        let refl_j = d.lemma(p.equiv_refl, &[of_nat_j]);
        let h_add = d.lemma(
            p.add_congr,
            &[
                of_nat_sn_i,
                mul_sn_i_term,
                of_nat_j,
                of_nat_j,
                step2,
                refl_j,
            ],
        );
        echain(d, p, of_nat_global, &[(mid, step1), (ofnat_split, h_add)])
    };

    // Step B : Equiv lhs a_mul_split_dmp.
    let lhs_step1 = {
        let refl_dmp = d.lemma(p.equiv_refl, &[delta_m_prime]);
        let h_mul = d.lemma(
            p.mul_congr,
            &[
                of_nat_global,
                ofnat_split,
                delta_m_prime,
                delta_m_prime,
                h_ofnat_global,
                refl_dmp,
            ],
        );
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        d.lemma(
            p.add_congr,
            &[a, a, mul_global_dmp, mul_split_dmp, refl_a, h_mul],
        )
    };

    // Step C : Equiv a_mul_split_dmp a_sum_parts, via `right_distrib`.
    let lhs_step2 = {
        let dist = right_distrib(d, p, mul_sn_i_term, of_nat_j, delta_m_prime);
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        d.lemma(p.add_congr, &[a, a, mul_split_dmp, sum_parts, refl_a, dist])
    };

    // Step D1 : Equiv term_j_part mul_j_fine, via the mesh identity.
    let h_j = {
        let refl_j = d.lemma(p.equiv_refl, &[of_nat_j]);
        d.lemma(
            p.mul_congr,
            &[
                of_nat_j,
                of_nat_j,
                delta_m_prime,
                delta_fine,
                refl_j,
                delta_eq,
            ],
        )
    };

    // Step D2 : Equiv term_i_part mul_i_dm, via `mul_comm`/`mul_assoc`
    // moving the `Nat.succ n` factor across to meet `mesh_count_width`.
    let h_i = {
        let comm_si = d.lemma(p.mul_comm, &[of_nat_sn, of_nat_i]);
        let mul_i_sn = cmul(d, p, of_nat_i, of_nat_sn);
        let refl_dmp = d.lemma(p.equiv_refl, &[delta_m_prime]);
        let step_a = d.lemma(
            p.mul_congr,
            &[
                mul_sn_i_term,
                mul_i_sn,
                delta_m_prime,
                delta_m_prime,
                comm_si,
                refl_dmp,
            ],
        );
        let mul_i_sn_dmp = cmul(d, p, mul_i_sn, delta_m_prime);

        let step_b = d.lemma(p.mul_assoc, &[of_nat_i, of_nat_sn, delta_m_prime]);
        let inner_sn_dmp = cmul(d, p, of_nat_sn, delta_m_prime);
        let target_b = cmul(d, p, of_nat_i, inner_sn_dmp);

        let refl_sn = d.lemma(p.equiv_refl, &[of_nat_sn]);
        let step_c = d.lemma(
            p.mul_congr,
            &[
                of_nat_sn,
                of_nat_sn,
                delta_m_prime,
                delta_fine,
                refl_sn,
                delta_eq,
            ],
        );
        let inner_sn_fine = cmul(d, p, of_nat_sn, delta_fine);
        let refl_i = d.lemma(p.equiv_refl, &[of_nat_i]);
        let step_c_lift = d.lemma(
            p.mul_congr,
            &[
                of_nat_i,
                of_nat_i,
                inner_sn_dmp,
                inner_sn_fine,
                refl_i,
                step_c,
            ],
        );
        let target_c = cmul(d, p, of_nat_i, inner_sn_fine);

        // mesh : Equiv inner_sn_fine delta_m -- `mesh_count_width(delta_m, n)`,
        // since `inner_sn_fine` is EXACTLY `mul (ofNat (succ n)) (mul delta_m
        // (embed (natDivSucc 1 n)))` up to argument order.
        let mesh = d.lemma(p.mesh_count_width, &[delta_m, n]);
        let step_d = d.lemma(
            p.mul_congr,
            &[of_nat_i, of_nat_i, inner_sn_fine, delta_m, refl_i, mesh],
        );

        echain(
            d,
            p,
            term_i_part,
            &[
                (mul_i_sn_dmp, step_a),
                (target_b, step_b),
                (target_c, step_c_lift),
                (mul_i_dm, step_d),
            ],
        )
    };

    // Step E : Equiv sum_parts target_sum.
    let h_split = d.lemma(
        p.add_congr,
        &[term_i_part, mul_i_dm, term_j_part, mul_j_fine, h_i, h_j],
    );

    // Step F : Equiv a_sum_parts a_target_sum.
    let lhs_step3 = {
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        d.lemma(p.add_congr, &[a, a, sum_parts, target_sum, refl_a, h_split])
    };

    // Step G : Equiv a_target_sum rhs, via `add_assoc(a, mul_i_dm,
    // mul_j_fine)` -- `base_i` is EXACTLY `add a mul_i_dm`, so `add base_i
    // mul_j_fine` is EXACTLY `rhs`, with no further rewrite needed.
    let g_step = {
        let assoc = d.lemma(p.add_assoc, &[a, mul_i_dm, mul_j_fine]);
        d.lemma(p.equiv_symm, &[rhs, a_target_sum, assoc])
    };

    let proof = echain(
        d,
        p,
        lhs,
        &[
            (a_mul_split_dmp, lhs_step1),
            (a_sum_parts, lhs_step2),
            (a_target_sum, lhs_step3),
            (rhs, g_step),
        ],
    );

    (lhs, rhs, proof)
}

/// `CReal.samplePoint_reblock : ∀ a b : CReal, ∀ n m i j : Nat, Equiv
/// (sample_point a delta_m_prime globalIdx) (sample_point base_i delta_fine
/// j)`, `delta_m_prime := mul (add b (neg a)) (embed (Rat.natDivSucc 1
/// m_prime))`, `m_prime := ((n·m)+n)+m` ([`succ_mul_succ`]'s own witness,
/// `Nat.succ m_prime` definitionally `(Nat.succ n)·(Nat.succ m)`),
/// `globalIdx := Nat.add (Nat.mul (Nat.succ n) i) j` (EXACTLY
/// `CReal.sumRange_reblock`'s own global fine index at block size `Nat.succ
/// n`, block index `i`), `base_i := sample_point a delta_m i`, `delta_m :=
/// mul (add b (neg a)) (embed (Rat.natDivSucc 1 m))`, `delta_fine := mul
/// delta_m (embed (Rat.natDivSucc 1 n))` (EXACTLY `CReal.fineSample_close`'s
/// own `fine_j`'s mesh at that same block).
///
/// This is roadmap step 1 toward `riemannSum_cauchy`'s common refinement:
/// `sumRange_reblock`'s conclusion applies an arbitrary `g` to the RAW
/// global index, while `fineBlockSum_close`'s own per-block sum applies `F`
/// at the LOCAL `base_i`/fine-offset arithmetic -- gluing the two needs
/// knowing these two sample points are the SAME real number. An
/// UNCONDITIONAL identity: no bound on `i`/`j` is needed at all, unlike
/// every other roadmap step (all of which place a sample point in `[a, b]`
/// and so need `i ≤ m`/`j < Nat.succ n`).
///
/// Route: [`mesh_reblock_delta_eq`] gives the exact mesh identity `delta_m_prime
/// ~ delta_fine` from `CReal.meshReciprocalMul`; `CReal.ofNat_add`/`ofNat_mul`
/// split `globalIdx` into `(Nat.succ n)*i + j`'s `CReal` shape;
/// `right_distrib` distributes the resulting sum times `delta_m_prime`;
/// `mul_comm`/`mul_assoc` move the `Nat.succ n` factor next to `delta_fine`
/// so `CReal.mesh_count_width` cancels it down to `delta_m`; `add_assoc`
/// closes the gap between the two additive re-groupings. See this file's own
/// module documentation and this section's header comment.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_sample_point_reblock(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let (lhs, rhs, proof) = sample_point_reblock_proof(d, p, a, b, n, m, i, j);
    let concl = equiv(d, p, lhs, rhs);

    let ty = {
        let over_j = d.pi_fv(j_fv, nat, concl);
        let over_i = d.pi_fv(i_fv, nat, over_j);
        let over_m = d.pi_fv(m_fv, nat, over_i);
        let over_n = d.pi_fv(n_fv, nat, over_m);
        let over_b = d.pi_fv(b_fv, carrier, over_n);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let with_j = d.lam_fv(j_fv, nat, proof);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        let with_m = d.lam_fv(m_fv, nat, with_i);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_b = d.lam_fv(b_fv, carrier, with_n);
        d.lam_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sample_point_reblock,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod sample_point_reblock_tests {
    use super::*;
    use crate::Declaration;
    use crate::rat_prelude::ops::{req, rrefl};

    /// **Mandatory concrete instantiation** (see the task briefing this
    /// module was built against, and its own caution that a symbolic build
    /// is necessary but a concrete one can still hide a transposed/sign
    /// defect a purely symbolic derivation would not): `n = 1, m = 2, i = 1,
    /// j = 1` (`n != m`, so a swapped `n`/`m` is visible), on `a = ofNat 1,
    /// b = ofNat 4` (`width = 3`, so a swapped `a`/`b` or a dropped `width`
    /// factor is visible too, unlike `width = 1`).
    ///
    /// By hand: `m_prime = n*m+n+m = 2+1+2 = 5`, `delta_m_prime =
    /// 3 * 1/6 = 1/2`, `globalIdx = (succ 1)*1+1 = 3`, LHS `= 1 + 3*(1/2) =
    /// 5/2`. `delta_m = 3 * 1/3 = 1`, `base_i = 1 + 1*1 = 2`, `delta_fine =
    /// 1 * 1/2 = 1/2`, RHS `= 2 + 1*(1/2) = 5/2`. Both `5/2`.
    ///
    /// Checked the same way `riemann_sum_of_the_constant_one_on_0_1_computes_to_one`
    /// (`creal_tests.rs`) checks `CReal.riemannSum`: `CReal.seq` of each side
    /// at a fixed index, `Eq Rat` closed by `Eq.refl` -- pure computation, no
    /// lemma, so a wrong index/mesh construction would leave the two sides
    /// stuck at DIFFERENT rationals and `add_declaration` would return `Err`.
    #[test]
    fn sample_point_reblock_computes_to_five_halves_at_concrete_args() {
        crate::on_a_deep_stack(sample_point_reblock_computes_to_five_halves_at_concrete_args_body);
    }

    fn sample_point_reblock_computes_to_five_halves_at_concrete_args_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let one_lit = d.num(1);
        let four_lit = d.num(4);
        let a = d.const_app(p.of_nat, &[one_lit]);
        let b = d.const_app(p.of_nat, &[four_lit]);
        let n = d.num(1);
        let m = d.num(2);
        let i = d.num(1);
        let j = d.num(1);

        let (lhs, rhs, _proof) = sample_point_reblock_proof(&mut d, p, a, b, n, m, i, j);

        let index = d.num(2);
        let lhs_seq = d.const_app(p.seq, &[lhs, index]);
        let rhs_seq = d.const_app(p.seq, &[rhs, index]);
        let stmt = req(&mut d, lhs_seq, rhs_seq);
        let proof = rrefl(&mut d, lhs_seq);

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "__sample_point_reblock_computes_to_five_halves");
        d.kernel()
            .add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty: stmt,
                value: proof,
            })
            .unwrap_or_else(|error| {
                panic!(
                    "sample_point_reblock's two sides did NOT compute to the \
                     same rational at n=1, m=2, i=1, j=1 (expected 5/2 both \
                     sides): {error:?}"
                )
            });
    }

    /// The general (symbolic `a, b, n, m, i, j`) proof, wrapped in its own
    /// anonymous theorem -- the same idiom `succ_shape_bridge_tests` above
    /// uses, and independent evidence beyond `creal_prelude_builds`'s own
    /// whole-prelude build that `sample_point_reblock_proof` produces a
    /// well-typed proof term at genuinely free variables, not just at the
    /// ground literals the test above uses.
    #[test]
    fn sample_point_reblock_type_checks_symbolically() {
        crate::on_a_deep_stack(sample_point_reblock_type_checks_symbolically_body);
    }

    fn sample_point_reblock_type_checks_symbolically_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);
        let nat = d.nat_ty();

        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let (lhs, rhs, proof) = sample_point_reblock_proof(&mut d, p, a, b, n, m, i, j);
        let concl = equiv(&mut d, p, lhs, rhs);

        let ty = {
            let over_j = d.pi_fv(j_fv, nat, concl);
            let over_i = d.pi_fv(i_fv, nat, over_j);
            let over_m = d.pi_fv(m_fv, nat, over_i);
            let over_n = d.pi_fv(n_fv, nat, over_m);
            let over_b = d.pi_fv(b_fv, carrier, over_n);
            d.pi_fv(a_fv, carrier, over_b)
        };
        let value = {
            let with_j = d.lam_fv(j_fv, nat, proof);
            let with_i = d.lam_fv(i_fv, nat, with_j);
            let with_m = d.lam_fv(m_fv, nat, with_i);
            let with_n = d.lam_fv(n_fv, nat, with_m);
            let with_b = d.lam_fv(b_fv, carrier, with_n);
            d.lam_fv(a_fv, carrier, with_b)
        };

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "__sample_point_reblock_symbolic_smoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "sample_point_reblock_proof must type-check at free variables: {:?}",
            result.err()
        );
    }
}

/// From `h1 : Equiv (add u v) zero` and `h2 : Equiv (add u w) zero`, derive
/// `Equiv v w` — additive inverses (of the SAME `u`) are unique up to
/// `Equiv`. Built from `add_assoc`/`add_comm`/`add_zero`/`add_congr` alone
/// (the standard group-theory cancellation argument), reused by
/// [`declare_equiv_abs_diff_le`] to identify `neg (add x (neg y))` with
/// `add y (neg x)` without a separate `neg` distributes-over-`add` law.
fn cancel_unique(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    w: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let uw = cadd(d, p, u, w);

    // step1 : Equiv v (add v zero).
    let vz = cadd(d, p, v, zero_c);
    let step1 = {
        let trim = d.lemma(p.add_zero, &[v]); // Equiv vz v
        d.lemma(p.equiv_symm, &[vz, v, trim])
    };

    // step2 : Equiv (add v zero) (add v uw), via `symm h2 : Equiv zero uw`.
    let v_uw = cadd(d, p, v, uw);
    let step2 = {
        let refl_v = d.lemma(p.equiv_refl, &[v]);
        let flip = d.lemma(p.equiv_symm, &[uw, zero_c, h2]); // Equiv zero uw
        d.lemma(p.add_congr, &[v, v, zero_c, uw, refl_v, flip])
    };

    // step3 : Equiv (add v uw) (add (add v u) w).
    let vu = cadd(d, p, v, u);
    let vu_w = cadd(d, p, vu, w);
    let step3 = {
        let assoc = d.lemma(p.add_assoc, &[v, u, w]); // Equiv vu_w v_uw
        d.lemma(p.equiv_symm, &[vu_w, v_uw, assoc])
    };

    // step4 : Equiv (add (add v u) w) (add (add u v) w).
    let uv = cadd(d, p, u, v);
    let uv_w = cadd(d, p, uv, w);
    let step4 = {
        let comm = d.lemma(p.add_comm, &[v, u]); // Equiv vu uv
        let refl_w = d.lemma(p.equiv_refl, &[w]);
        d.lemma(p.add_congr, &[vu, uv, w, w, comm, refl_w])
    };

    // step5 : Equiv (add (add u v) w) (add zero w), via h1.
    let zero_w = cadd(d, p, zero_c, w);
    let step5 = {
        let refl_w = d.lemma(p.equiv_refl, &[w]);
        d.lemma(p.add_congr, &[uv, zero_c, w, w, h1, refl_w])
    };

    // step6 : Equiv (add zero w) (add w zero).
    let w_zero = cadd(d, p, w, zero_c);
    let step6 = d.lemma(p.add_comm, &[zero_c, w]);

    // step7 : Equiv (add w zero) w.
    let step7 = d.lemma(p.add_zero, &[w]);

    echain(
        d,
        p,
        v,
        &[
            (vz, step1),
            (v_uw, step2),
            (vu_w, step3),
            (uv_w, step4),
            (zero_w, step5),
            (w_zero, step6),
            (w, step7),
        ],
    )
}

/// `CReal.equivAbsDiffLe : ∀ x y : CReal, Equiv x y → ∀ e : Nat,
/// le (abs (add x (neg y))) (embed (Rat.natDivSucc 1 e))` — two REAL-EQUAL
/// numbers are within ANY chosen rational bound of each other. The general
/// fact `riemannSum_cauchy`'s common refinement needs to promote "the global
/// fine sample point IS the local block sample point" (an EXACT `Equiv`,
/// from pure sample-point arithmetic) into the EXPLICIT, computable distance
/// bound `UniformlyContinuousOn.spec` demands as a hypothesis — no
/// Archimedean threshold on `e` at all, since `Equiv` already gives
/// arbitrary precision for free.
///
/// Route: `le_of_equiv` (both directions, the second via `equiv_symm`) gives
/// `le x y` and `le y x`; each widens (via `add_le_add`/`add_neg`/`le_congr`,
/// the same shape [`width_nonneg_of`] uses) to `le (add x (neg y)) zero` and
/// `le (add y (neg x)) zero`; `frac_nonneg` and `le_trans` push both up to
/// the target bound `embed (natDivSucc 1 e)`. [`cancel_unique`] identifies
/// `neg (add x (neg y))` with `add y (neg x)` (both are additive inverses of
/// `add x (neg y)`, so this needs no `neg`-distributes-over-`add` law), and
/// `le_congr` transports the second bound across that identity; `abs_le`
/// closes both into one.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_equiv_abs_diff_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let hxy_ty = equiv(d, p, x, y);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let diff = {
        let ny = cneg(d, p, y);
        cadd(d, p, x, ny)
    };
    let flipped = {
        let nx = cneg(d, p, x);
        cadd(d, p, y, nx)
    };
    let neg_diff = cneg(d, p, diff);
    let zero_c = czero(d, p);

    // d1 : le diff zero.
    let d1 = {
        let ny = cneg(d, p, y);
        let hxy_le = d.lemma(p.le_of_equiv, &[x, y, hxy]);
        let refl_ny = d.lemma(p.le_refl, &[ny]);
        let y_ny = cadd(d, p, y, ny);
        let shifted = d.lemma(p.add_le_add, &[x, y, ny, ny, hxy_le, refl_ny]);
        // shifted : le diff y_ny
        let hn = d.lemma(p.add_neg, &[y]); // Equiv y_ny zero
        let refl_diff = d.lemma(p.equiv_refl, &[diff]);
        d.lemma(
            p.le_congr,
            &[diff, diff, y_ny, zero_c, refl_diff, hn, shifted],
        )
    };

    // d2 : le flipped zero.
    let d2 = {
        let hyx = d.lemma(p.equiv_symm, &[x, y, hxy]);
        let hyx_le = d.lemma(p.le_of_equiv, &[y, x, hyx]);
        let nx = cneg(d, p, x);
        let refl_nx = d.lemma(p.le_refl, &[nx]);
        let x_nx = cadd(d, p, x, nx);
        let shifted = d.lemma(p.add_le_add, &[y, x, nx, nx, hyx_le, refl_nx]);
        // shifted : le flipped x_nx
        let hn = d.lemma(p.add_neg, &[x]); // Equiv x_nx zero
        let refl_flipped = d.lemma(p.equiv_refl, &[flipped]);
        d.lemma(
            p.le_congr,
            &[flipped, flipped, x_nx, zero_c, refl_flipped, hn, shifted],
        )
    };

    let embed_q = {
        let one_nat = d.num(1);
        let q = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
        embed(d, p, q)
    };
    let q_nonneg = frac_nonneg(d, p, e);

    let upper = d.lemma(p.le_trans, &[diff, zero_c, embed_q, d1, q_nonneg]);
    let lower_flipped = d.lemma(p.le_trans, &[flipped, zero_c, embed_q, d2, q_nonneg]);

    // neg_diff_eq : Equiv flipped neg_diff, both are additive inverses of
    // `diff` (`h_sum_zero : Equiv (add diff flipped) zero` below, and
    // `add_neg(diff) : Equiv (add diff neg_diff) zero`).
    let h_sum_zero = {
        let ny = cneg(d, p, y);
        let nx = cneg(d, p, x);
        let start = cadd(d, p, diff, flipped); // (x + (-y)) + (y + (-x))

        // s1 := add x (add (neg y) flipped).
        let inner0 = cadd(d, p, ny, flipped);
        let s1 = cadd(d, p, x, inner0);
        let h1 = d.lemma(p.add_assoc, &[x, ny, flipped]); // Equiv start s1 (direct)

        // inner chain: (neg y) + flipped ~ ((neg y)+y) + (neg x) ~ zero + (neg x) ~ neg x.
        let ny_y = cadd(d, p, ny, y);
        let inner1 = cadd(d, p, ny_y, nx);
        let h_inner_assoc = {
            // add_assoc(neg y, y, neg x) : Equiv inner1 inner0
            let assoc = d.lemma(p.add_assoc, &[ny, y, nx]);
            d.lemma(p.equiv_symm, &[inner1, inner0, assoc])
        };
        // h_inner_assoc : Equiv inner0 inner1

        let ny_y_zero = {
            let comm = d.lemma(p.add_comm, &[ny, y]); // Equiv ny_y (add y ny)
            let y_ny = cadd(d, p, y, ny);
            let hn = d.lemma(p.add_neg, &[y]); // Equiv y_ny zero
            d.lemma(p.equiv_trans, &[ny_y, y_ny, zero_c, comm, hn])
        };
        // ny_y_zero : Equiv ny_y zero

        let zero_nx = cadd(d, p, zero_c, nx);
        let h_inner2 = {
            let refl_nx = d.lemma(p.equiv_refl, &[nx]);
            d.lemma(p.add_congr, &[ny_y, zero_c, nx, nx, ny_y_zero, refl_nx])
        };
        // h_inner2 : Equiv inner1 zero_nx

        let h_inner3 = {
            let comm = d.lemma(p.add_comm, &[zero_c, nx]); // Equiv zero_nx (add nx zero)
            let nx_zero = cadd(d, p, nx, zero_c);
            let trim = d.lemma(p.add_zero, &[nx]); // Equiv nx_zero nx
            d.lemma(p.equiv_trans, &[zero_nx, nx_zero, nx, comm, trim])
        };
        // h_inner3 : Equiv zero_nx nx

        let inner_eq = echain(
            d,
            p,
            inner0,
            &[(inner1, h_inner_assoc), (zero_nx, h_inner2), (nx, h_inner3)],
        );
        // inner_eq : Equiv inner0 nx

        let h6 = {
            let refl_x = d.lemma(p.equiv_refl, &[x]);
            d.lemma(p.add_congr, &[x, x, inner0, nx, refl_x, inner_eq])
        };
        // h6 : Equiv s1 (add x nx)

        let x_nx = cadd(d, p, x, nx);
        let h7 = d.lemma(p.add_neg, &[x]); // Equiv x_nx zero

        echain(d, p, start, &[(s1, h1), (x_nx, h6), (zero_c, h7)])
    };
    let h_self_zero = d.lemma(p.add_neg, &[diff]); // Equiv (add diff neg_diff) zero

    let raw = cancel_unique(d, p, diff, flipped, neg_diff, h_sum_zero, h_self_zero);
    // raw : Equiv flipped neg_diff

    let lower = {
        let refl_q = d.lemma(p.equiv_refl, &[embed_q]);
        d.lemma(
            p.le_congr,
            &[
                flipped,
                neg_diff,
                embed_q,
                embed_q,
                raw,
                refl_q,
                lower_flipped,
            ],
        )
    };

    let proof_body = d.lemma(p.abs_le, &[diff, embed_q, upper, lower]);

    let ty = {
        let abs_diff = d.const_app(p.abs, &[diff]);
        let concl = cle(d, p, abs_diff, embed_q);
        let after_e = d.pi_fv(e_fv, nat, concl);
        let after_hxy = d.arrow(hxy_ty, after_e);
        let over_y = d.pi_fv(y_fv, carrier, after_hxy);
        d.pi_fv(x_fv, carrier, over_y)
    };
    let value = {
        let with_e = d.lam_fv(e_fv, nat, proof_body);
        let with_hxy = d.lam_fv(hxy_fv, hxy_ty, with_e);
        let over_y = d.lam_fv(y_fv, carrier, with_hxy);
        d.lam_fv(x_fv, carrier, over_y)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_abs_diff_le,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the archimedean rescaling: Δ_m into a UniformlyContinuousOn-shaped bound

/// From `hab : le a b`, derive `le zero (width_of a b)` — `b − a ≥ 0`.
/// Reproduces `monotone.rs`'s private `step_nonneg_of`'s `width_nonneg`
/// fragment (that function bundles it with a `frac_real` factor this call
/// site does not need).
fn width_nonneg_of(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    hab: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let na = cneg(d, p, a);
    let refl_na = d.lemma(p.le_refl, &[na]);
    let a_na = cadd(d, p, a, na);
    let b_na = cadd(d, p, b, na);
    let shifted = d.lemma(p.add_le_add, &[a, b, na, na, hab, refl_na]);
    let hn = d.lemma(p.add_neg, &[a]);
    let refl_bna = d.lemma(p.equiv_refl, &[b_na]);
    d.lemma(
        p.le_congr,
        &[a_na, zero_c, b_na, b_na, hn, refl_bna, shifted],
    )
}

/// `CReal.bound x`, `CReal.bound x + 1`, and a DIRECT proof of `le x (ofNat
/// (bound x + 1))` — reproduces `archimedean.rs`'s private `le_proof` (inside
/// `declare_archimedean_property`), generalized to an arbitrary `x`.
/// `CReal.bound` is a total COMPUTABLE projection (`archimedean.rs`'s own
/// module documentation), so this needs no existential elimination at all:
/// the witness `bound x + 1` is read directly off `x`, unlike
/// `monotone_of_nonneg_deriv`'s Archimedean closing step, which eliminates
/// `p.archimedean`'s `∃ n, …` to obtain its bound.
///
/// Returns `(c, magnitude, proof)` with `magnitude = Nat.succ c`,
/// `c = CReal.bound x`, `proof : CReal.le x (CReal.ofNat magnitude)`.
fn direct_bound_le(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> (ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let nat = d.nat_ty();

    let c = d.const_app(p.bound, &[x]);
    let magnitude = d.succ(c);
    let zero_nat = d.num(0);
    let target = d.const_app(rat.nat_div_succ, &[magnitude, zero_nat]);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let point = sample(d, p, x, k);
    let bw = d.lemma(p.bound_within, &[x, k]);
    let (_, upper) = halves(d, p, point, target, bw);

    let two_nat = d.num(2);
    let bound2 = d.const_app(rat.nat_div_succ, &[two_nat, k]);
    let nonneg2 = d.lemma(rat.zero_le_nat_div_succ, &[two_nat, k]);

    let zero = rzero(d, rat);
    let target_refl = d.lemma(rat.le_refl, &[target]);
    let widened = d.lemma(
        rat.add_le_add,
        &[target, target, zero, bound2, target_refl, nonneg2],
    );
    let padded_target = radd(d, target, zero);
    let sum = radd(d, target, bound2);
    let trim = d.lemma(rat.add_zero, &[target]);
    let target_le_sum = rat_eq_rewrite(d, padded_target, target, trim, widened, &|d, t| {
        rle(d, rat, t, sum)
    });

    let chained = d.lemma(rat.le_trans, &[point, target, sum, upper, target_le_sum]);
    let at_index = d.lemma(rat.sub_le_of_le, &[point, target, bound2, chained]);
    let proof_body = d.lam_fv(k_fv, nat, at_index);
    (c, magnitude, proof_body)
}

/// `Equiv (mul (ofNat magnitude) (ofRat (natDivSucc 1 deep))) (ofRat
/// (natDivSucc 1 outer))`, given `magnitude = Nat.succ c` and `deep =
/// magnitude*outer + c` (a SYNTACTIC requirement: `Rat.natDivSucc_scale` is
/// applied at `(c, outer)` and its conclusion must match `deep` on the
/// nose). Duplicated verbatim from `monotone.rs`'s private
/// `magnitude_times_frac_eq_outer` (that file is out of scope for this
/// slice).
fn magnitude_times_frac_eq_outer(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    magnitude: ExprId,
    outer: ExprId,
    deep: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = rat.int.nat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);

    let mag_rat = d.const_app(rat.nat_div_succ, &[magnitude, zero_nat]);
    let frac_rat = d.const_app(rat.nat_div_succ, &[one_nat, deep]);
    let mag_real = embed(d, p, mag_rat);
    let frac_real = embed(d, p, frac_rat);
    let product_real = cmul(d, p, mag_real, frac_real);

    let product_rat = rmul(d, mag_rat, frac_rat);
    let fused = {
        let scaled = NatOps::mul(d, magnitude, one_nat);
        d.const_app(rat.nat_div_succ, &[scaled, deep])
    };
    let fuse = d.lemma(rat.nat_div_succ_mul, &[magnitude, one_nat, deep]);
    let collapsed = d.const_app(rat.nat_div_succ, &[magnitude, deep]);
    let collapse = {
        let scaled = NatOps::mul(d, magnitude, one_nat);
        let identity = d.lemma(nat.mul_one, &[magnitude]);
        nat_eq_to_rat(d, scaled, magnitude, identity, &|d, t| {
            d.const_app(rat.nat_div_succ, &[t, deep])
        })
    };
    let outer_rat = d.const_app(rat.nat_div_succ, &[one_nat, outer]);
    let scale = d.lemma(rat.nat_div_succ_scale, &[c, outer]);
    // scale : Eq Rat (natDivSucc magnitude deep) (natDivSucc 1 outer),
    // PROVIDED `deep` is exactly `mul(magnitude, outer) + c`.

    let (_, chain) = rchain(
        d,
        product_rat,
        &[(fused, fuse), (collapsed, collapse), (outer_rat, scale)],
    );

    let of_rat_mul_step = d.lemma(p.of_rat_mul, &[mag_rat, frac_rat]);
    rat_eq_rewrite(
        d,
        product_rat,
        outer_rat,
        chain,
        of_rat_mul_step,
        &|d, t| {
            let embedded = embed(d, p, t);
            equiv(d, p, product_real, embedded)
        },
    )
}

/// `le (mul diff (ofRat (natDivSucc 1 deep))) (ofRat (natDivSucc 1 outer))`,
/// given `diff_le_mag : le diff (ofNat magnitude)`, `magnitude = Nat.succ
/// c`, `deep = magnitude*outer + c`. Duplicated verbatim from `monotone.rs`'s
/// private `step_le_outer_bound` (that file is out of scope for this
/// slice) — the numeric heart of the Archimedean scaling this file's
/// `mesh_le_of_ge` needs.
#[allow(clippy::too_many_arguments)]
fn step_le_outer_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    diff: ExprId,
    diff_le_mag: ExprId,
    c: ExprId,
    magnitude: ExprId,
    outer: ExprId,
    deep: ExprId,
) -> ExprId {
    let one_nat = d.num(1);
    let frac_deep_rat = div_succ(d, p, 1, deep);
    let frac_deep = embed(d, p, frac_deep_rat);
    let frac_nonneg = {
        let rzero_expr = d.kernel().const_(p.rat.zero, vec![]);
        let rle_p = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, deep]);
        d.lemma(p.of_rat_le, &[rzero_expr, frac_deep_rat, rle_p])
    };

    let step = cmul(d, p, diff, frac_deep);
    let diff_frac = cmul(d, p, frac_deep, diff);
    let comm1 = d.lemma(p.mul_comm, &[diff, frac_deep]);

    let om = d.const_app(p.of_nat, &[magnitude]);
    let mag_frac = cmul(d, p, frac_deep, om);
    let scaled = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[frac_deep, diff, om, frac_nonneg, diff_le_mag],
    );

    let refl_mag_frac = d.lemma(p.equiv_refl, &[mag_frac]);
    let comm1_symm = d.lemma(p.equiv_symm, &[step, diff_frac, comm1]);
    let step_le_mag_frac = d.lemma(
        p.le_congr,
        &[
            diff_frac,
            step,
            mag_frac,
            mag_frac,
            comm1_symm,
            refl_mag_frac,
            scaled,
        ],
    );

    let frac_mag = cmul(d, p, om, frac_deep);
    let comm2 = d.lemma(p.mul_comm, &[frac_deep, om]);
    let collapse = magnitude_times_frac_eq_outer(d, p, c, magnitude, outer, deep);
    let out_bound_rat = div_succ(d, p, 1, outer);
    let out_bound = embed(d, p, out_bound_rat);
    let mag_frac_eq_out = d.lemma(
        p.equiv_trans,
        &[mag_frac, frac_mag, out_bound, comm2, collapse],
    );

    let refl_step = d.lemma(p.equiv_refl, &[step]);
    d.lemma(
        p.le_congr,
        &[
            step,
            step,
            mag_frac,
            out_bound,
            refl_step,
            mag_frac_eq_out,
            step_le_mag_frac,
        ],
    )
}

/// `CReal.mesh_le_of_ge : ∀ a b outer m, le a b → Nat.le ((Nat.succ (bound
/// (add b (neg a))))*outer + bound (add b (neg a))) m → le (mul (add b (neg
/// a)) (ofRat (natDivSucc 1 m))) (ofRat (natDivSucc 1 outer))` — the
/// ARCHIMEDEAN RESCALING `UniformlyContinuousOn.spec` needs: turning the
/// mesh width `Δ_m := (b−a)·natDivSucc(1,m)` into a bound of the exact
/// rational shape `natDivSucc 1 outer` that spec expects, for EVERY block
/// count `m` at or past a computed threshold.
///
/// The threshold and the estimate reuse the SAME construction
/// `monotone.rs`'s `HasDerivativeOn`-based Archimedean closing step uses
/// ([`step_le_outer_bound`]/[`magnitude_times_frac_eq_outer`], duplicated
/// here since that file is out of scope for this slice) — but where that
/// proof is free to pick its OWN subdivision count, this one is handed an
/// arbitrary `m` already at least as large as the threshold (`riemannSum`'s
/// block count is fixed by its caller, not chosen here), so an extra
/// `Rat.natDivSucc_antitone` step widens the exact-threshold bound across
/// the gap. No existential elimination anywhere: [`direct_bound_le`] reads
/// the Archimedean witness directly off `CReal.bound`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
fn declare_mesh_le_of_ge(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let outer_fv = d.fresh_fvar();
    let outer = d.kernel().fvar(outer_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let width = width_of(d, p, a, b);
    let (c, magnitude, width_le_mag) = direct_bound_le(d, p, width);
    let me = NatOps::mul(d, magnitude, outer);
    let deep = NatOps::add(d, me, c);

    let hge_ty = d.le(deep, m);
    let hge_fv = d.fresh_fvar();
    let hge = d.kernel().fvar(hge_fv);

    let width_nonneg = width_nonneg_of(d, p, a, b, hab);
    let bound_at_deep = step_le_outer_bound(d, p, width, width_le_mag, c, magnitude, outer, deep);

    let one_nat = d.num(1);
    let frac_m_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_deep_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, deep]);
    let out_bound_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, outer]);

    let antitone = d.lemma(p.rat.nat_div_succ_antitone, &[deep, m, hge]);
    let frac_le_real = d.lemma(p.of_rat_le, &[frac_m_rat, frac_deep_rat, antitone]);

    let frac_m_real = embed(d, p, frac_m_rat);
    let frac_deep_real = embed(d, p, frac_deep_rat);
    let out_bound = embed(d, p, out_bound_rat);

    let scaled = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[
            width,
            frac_m_real,
            frac_deep_real,
            width_nonneg,
            frac_le_real,
        ],
    );

    let step_m = cmul(d, p, width, frac_m_real);
    let step_deep = cmul(d, p, width, frac_deep_real);
    let final_le = d.lemma(
        p.le_trans,
        &[step_m, step_deep, out_bound, scaled, bound_at_deep],
    );

    let concl = cle(d, p, step_m, out_bound);
    let ty = {
        let after_hge = d.arrow(hge_ty, concl);
        let after_hab = d.arrow(hab_ty, after_hge);
        let over_m = d.pi_fv(m_fv, nat, after_hab);
        let over_outer = d.pi_fv(outer_fv, nat, over_m);
        let over_b = d.pi_fv(b_fv, carrier, over_outer);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let with_hge = d.lam_fv(hge_fv, hge_ty, final_le);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hge);
        let over_m = d.lam_fv(m_fv, nat, with_hab);
        let over_outer = d.lam_fv(outer_fv, nat, over_m);
        let over_b = d.lam_fv(b_fv, carrier, over_outer);
        d.lam_fv(a_fv, carrier, over_b)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_le_of_ge,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit [`CRealPrelude::mesh_scaled_le_of_ge`]. See that field's own doc
/// comment for the statement and the route: reuse [`declare_mesh_le_of_ge`]
/// wholesale at a substituted `outer' := k*outer + k0`, scale by the nonneg
/// `k := Nat.succ k0`, then collapse `k·(1/(outer'+1))` back to
/// `1/(outer+1)` with [`magnitude_times_frac_eq_outer`] at `c := k0`,
/// `magnitude := k`, `deep := outer'`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
fn declare_mesh_scaled_le_of_ge(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let outer_fv = d.fresh_fvar();
    let outer = d.kernel().fvar(outer_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k0_fv = d.fresh_fvar();
    let k0 = d.kernel().fvar(k0_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let width = width_of(d, p, a, b);
    let (c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);

    // k := Nat.succ k0, outer' := k*outer + k0 -- exactly the syntactic
    // shape `Rat.natDivSucc_scale` (via `magnitude_times_frac_eq_outer`)
    // needs at `(c, magnitude, deep) := (k0, k, outer')`.
    let k = d.succ(k0);
    let k_outer = NatOps::mul(d, k, outer);
    let outer_prime = NatOps::add(d, k_outer, k0);

    // hge_ty : Nat.le (magnitude*outer' + c) m -- EXACTLY `mesh_le_of_ge`'s
    // own hypothesis shape with `outer` substituted by `outer'`, so
    // `mesh_le_of_ge` applies wholesale below.
    let me = NatOps::mul(d, magnitude, outer_prime);
    let deep = NatOps::add(d, me, c);
    let hge_ty = d.le(deep, m);
    let hge_fv = d.fresh_fvar();
    let hge = d.kernel().fvar(hge_fv);

    // mesh_result : le (mul width (ofRat (natDivSucc 1 m)))
    //                  (ofRat (natDivSucc 1 outer'))
    let mesh_result = d.lemma(p.mesh_le_of_ge, &[a, b, outer_prime, m, hab, hge]);

    let one_nat = d.num(1);
    let frac_m_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_m_real = embed(d, p, frac_m_rat);
    let step_m = cmul(d, p, width, frac_m_real);

    let out_bound_prime_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, outer_prime]);
    let out_bound_prime = embed(d, p, out_bound_prime_rat);

    let k_real = d.const_app(p.of_nat, &[k]);
    let k_nonneg = zero_le_of_nat(d, p, k);

    // scaled : le (mul k_real step_m) (mul k_real out_bound_prime)
    let scaled = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[k_real, step_m, out_bound_prime, k_nonneg, mesh_result],
    );

    // collapse : Equiv (mul (ofNat k) (ofRat (natDivSucc 1 outer')))
    //                  (ofRat (natDivSucc 1 outer))
    let collapse = magnitude_times_frac_eq_outer(d, p, k0, k, outer, outer_prime);

    let out_bound_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, outer]);
    let out_bound = embed(d, p, out_bound_rat);

    let k_step_m = cmul(d, p, k_real, step_m);
    let k_out_bound_prime = cmul(d, p, k_real, out_bound_prime);
    let refl_k_step_m = d.lemma(p.equiv_refl, &[k_step_m]);
    let final_le = d.lemma(
        p.le_congr,
        &[
            k_step_m,
            k_step_m,
            k_out_bound_prime,
            out_bound,
            refl_k_step_m,
            collapse,
            scaled,
        ],
    );

    let concl = cle(d, p, k_step_m, out_bound);
    let ty = {
        let after_hge = d.arrow(hge_ty, concl);
        let after_hab = d.arrow(hab_ty, after_hge);
        let over_k0 = d.pi_fv(k0_fv, nat, after_hab);
        let over_m = d.pi_fv(m_fv, nat, over_k0);
        let over_outer = d.pi_fv(outer_fv, nat, over_m);
        let over_b = d.pi_fv(b_fv, carrier, over_outer);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let with_hge = d.lam_fv(hge_fv, hge_ty, final_le);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hge);
        let over_k0 = d.lam_fv(k0_fv, nat, with_hab);
        let over_m = d.lam_fv(m_fv, nat, over_k0);
        let over_outer = d.lam_fv(outer_fv, nat, over_m);
        let over_b = d.lam_fv(b_fv, carrier, over_outer);
        d.lam_fv(a_fv, carrier, over_b)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_scaled_le_of_ge,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the per-term fine-vs-coarse sample bound -- toward `riemannSum_cauchy`'s
// common refinement (roadmap step 1)
//
// Comparing one coarse block's single term against its `succ n` fine
// sub-terms needs every fine sample point in that block to lie within
// `delta_outer` (the COARSE mesh) of the block's own coarse sample point,
// regardless of which fine index `j < succ n` or which coarse block it is —
// this section's own module documentation numbers this "step 1" and flags it
// as a success on its own. `delta_outer` here instantiates to `riemannSum`'s
// own `Δ_m` (this file's `delta_of`) at the call site that uses this; kept
// abstract here since nothing below reads `a`/`b`, only `delta_outer`'s own
// nonnegativity.

/// `Equiv (add (add x w) (neg x)) w` — `(x + w) − x ~ w`. The mirror of
/// [`add_sub_cancel`] (`a + (b − a) ~ b`): here the FIRST operand of the
/// addition is the one subtracted back off, rather than the second.
fn cancel_add_neg_right(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, w: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let xw = cadd(d, p, x, w); // x + w
    let start = cadd(d, p, xw, nx); // (x + w) + (-x)

    let wx = cadd(d, p, w, x); // w + x
    let s1 = cadd(d, p, wx, nx); // (w + x) + (-x)
    let h1 = {
        let comm = d.lemma(p.add_comm, &[x, w]); // Equiv xw wx
        let refl_nx = d.lemma(p.equiv_refl, &[nx]);
        d.lemma(p.add_congr, &[xw, wx, nx, nx, comm, refl_nx])
        // : Equiv start s1
    };

    let xnx = cadd(d, p, x, nx); // x + (-x)
    let s2 = cadd(d, p, w, xnx); // w + (x + (-x))
    let h2 = d.lemma(p.add_assoc, &[w, x, nx]); // Equiv s1 s2

    let zero_c = czero(d, p);
    let s3 = cadd(d, p, w, zero_c); // w + zero
    let h3 = {
        let hn = d.lemma(p.add_neg, &[x]); // Equiv xnx zero_c
        let refl_w = d.lemma(p.equiv_refl, &[w]);
        d.lemma(p.add_congr, &[w, w, xnx, zero_c, refl_w, hn])
        // : Equiv s2 s3
    };

    let h4 = d.lemma(p.add_zero, &[w]); // Equiv s3 w

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (w, h4)])
}

/// From `v_nonneg : le zero v` and `bound_nonneg : le zero bound`, `le (neg
/// v) bound`. Reproduced verbatim from `derivative.rs`'s private
/// `neg_le_of_nonneg` (that file is out of scope for this slice).
fn neg_le_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    bound: ExprId,
    v_nonneg: ExprId,
    bound_nonneg: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let neg_v = cneg(d, p, v);
    let neg_zero = cneg(d, p, zero_c);

    let step = d.lemma(p.neg_le_neg, &[zero_c, v, v_nonneg]);
    // step : le neg_v neg_zero
    let nz_eq = {
        // `Equiv (neg zero) zero`, reproduced verbatim from several modules'
        // private `neg_zero_equiv` (e.g. `derivative.rs`) since this file
        // cannot call any of them.
        let nz = cneg(d, p, zero_c);
        let padded = cadd(d, p, nz, zero_c);
        let flipped = cadd(d, p, zero_c, nz);
        let ha = d.lemma(p.add_zero, &[nz]); // padded ~ nz
        let step1 = d.lemma(p.equiv_symm, &[padded, nz, ha]); // nz ~ padded
        let hb = d.lemma(p.add_comm, &[nz, zero_c]); // padded ~ flipped
        let hc = d.lemma(p.add_neg, &[zero_c]); // flipped ~ zero_c
        echain(d, p, nz, &[(padded, step1), (flipped, hb), (zero_c, hc)])
    };
    let refl_negv = d.lemma(p.equiv_refl, &[neg_v]);
    let le_negv_zero = d.lemma(
        p.le_congr,
        &[neg_v, neg_v, neg_zero, zero_c, refl_negv, nz_eq, step],
    );
    // le_negv_zero : le neg_v zero_c

    d.lemma(
        p.le_trans,
        &[neg_v, zero_c, bound, le_negv_zero, bound_nonneg],
    )
}

/// `le zero (embed (natDivSucc 1 denom))` — the mesh fraction `1/(denom+1)`
/// is always nonneg. The same route [`delta_nonneg_of`]'s own `frac_nonneg`
/// uses, factored out so [`sample_offset_bound`] can call it at the FINE
/// denominator `n` independently of that function's coarse `m`.
fn frac_nonneg(d: &mut IntDev<'_>, p: CRealPrelude, denom: ExprId) -> ExprId {
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, denom]);
    let rzero_expr = rzero(d, p.rat);
    let rle_p = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, denom]);
    d.lemma(p.of_rat_le, &[rzero_expr, frac, rle_p])
}

/// `(term, term_nonneg, term_le_delta)`, `term := mul (ofNat j) delta_fine`,
/// `delta_fine := mul delta (embed (Rat.natDivSucc 1 n))`, `term_nonneg :
/// le zero term`, `term_le_delta : le term delta` — the pure NUMERIC core
/// [`sample_offset_bound`]'s own proof needs (there, to close an `abs_le`)
/// and the fine-sample placement lemma [`declare_fine_sample_in_bounds`]
/// needs directly (there, to place the fine sample point between `base` and
/// `base + delta` via [`shift_le_of_nonneg`]/`add_le_add`). Factored out so
/// both share exactly this proof term rather than two independently-typed
/// copies of it.
fn fine_term_and_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    delta: ExprId,
    n: ExprId,
    j: ExprId,
    hlt: ExprId,
    delta_nonneg: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let one_nat = d.num(1);
    let frac_n_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
    let frac_n = embed(d, p, frac_n_rat);
    let delta_fine = cmul(d, p, delta, frac_n); // Δ_fine := delta * natDivSucc 1 n
    let of_nat_j = d.const_app(p.of_nat, &[j]);
    let term = cmul(d, p, of_nat_j, delta_fine); // mul (ofNat j) delta_fine

    let frac_n_nonneg = frac_nonneg(d, p, n);
    let delta_fine_nonneg = d.lemma(p.mul_nonneg, &[delta, frac_n, delta_nonneg, frac_n_nonneg]);

    // term_nonneg : le zero term.
    let term_nonneg = {
        let j_nonneg = zero_le_of_nat(d, p, j);
        d.lemma(
            p.mul_nonneg,
            &[of_nat_j, delta_fine, j_nonneg, delta_fine_nonneg],
        )
    };

    // term_le_delta : le term delta.
    let term_le_delta = {
        let n_succ = d.succ(n);
        let hle_j_n = nat_le_of_lt(d, j, n_succ, hlt); // Nat.le j (succ n)
        let of_nat_n_succ = d.const_app(p.of_nat, &[n_succ]);
        let j_le_n_succ = d.lemma(p.of_nat_le, &[j, n_succ, hle_j_n]); // le (ofNat j) (ofNat (succ n))

        let step = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[
                delta_fine,
                of_nat_j,
                of_nat_n_succ,
                delta_fine_nonneg,
                j_le_n_succ,
            ],
        );
        // step : le (mul delta_fine (ofNat j)) (mul delta_fine (ofNat n_succ))
        let comm_j = d.lemma(p.mul_comm, &[delta_fine, of_nat_j]);
        let comm_n = d.lemma(p.mul_comm, &[delta_fine, of_nat_n_succ]);
        let dj = cmul(d, p, delta_fine, of_nat_j);
        let dn = cmul(d, p, delta_fine, of_nat_n_succ);
        let nd = cmul(d, p, of_nat_n_succ, delta_fine);
        let commuted = d.lemma(p.le_congr, &[dj, term, dn, nd, comm_j, comm_n, step]);
        // commuted : le term nd, term = mul (ofNat j) delta_fine

        // n_delta_eq_delta : Equiv (mul (ofNat (succ n)) (mul delta frac_n)) delta
        //                  = Equiv nd delta, since `delta_fine` is exactly
        //   `mul delta frac_n` and `nd` is exactly `mul (ofNat (succ n)) delta_fine`.
        let n_delta_eq_delta = mesh_times_count_eq_width(d, p, delta, frac_n, n);

        let refl_term = d.lemma(p.equiv_refl, &[term]);
        d.lemma(
            p.le_congr,
            &[term, term, nd, delta, refl_term, n_delta_eq_delta, commuted],
        )
        // : le term delta
    };

    (term, term_nonneg, term_le_delta)
}

/// `CReal.le (CReal.abs (CReal.add (CReal.add base (CReal.mul (CReal.ofNat
/// j) (CReal.mul delta (CReal.ofRat (Rat.natDivSucc 1 n))))) (CReal.neg
/// base))) delta` — roadmap step 1: every fine sample point `base +
/// j·Δ_fine` (`Δ_fine := delta · natDivSucc 1 n`, `j < succ n`) lies within
/// `delta` of the block's own coarse sample point `base`, for an arbitrary
/// nonneg `delta` — independent of which coarse block `base` names.
///
/// Route: [`cancel_add_neg_right`] collapses the difference to the pure
/// offset term `mul (ofNat j) Δ_fine`; that term is nonneg (`ofNat j` and
/// `Δ_fine` both nonneg, `mul_nonneg`) and bounded above by `delta` exactly
/// via `j ≤ succ n` ([`nat_le_of_lt`] on the hypothesis `hlt`), `ofNat_le`,
/// `mul_le_mul_of_nonneg_left` and the exact identity `(succ n)·Δ_fine ~
/// delta` ([`mesh_times_count_eq_width`] at `(delta, frac_n, n)` — the same
/// helper [`declare_riemann_sample_in_bounds`]'s `upper` branch already
/// uses, here reused at the FINE denominator rather than the coarse one);
/// [`neg_le_of_nonneg`] gives the other `abs_le` branch directly from that
/// same nonnegativity, with no separate lower-bound argument needed.
fn sample_offset_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    base: ExprId,
    delta: ExprId,
    n: ExprId,
    j: ExprId,
    hlt: ExprId,
    delta_nonneg: ExprId,
) -> ExprId {
    let (term, term_nonneg, term_le_delta) =
        fine_term_and_bounds(d, p, delta, n, j, hlt, delta_nonneg);

    let x_j = cadd(d, p, base, term); // base + term -- the fine sample point
    let diff = {
        let nb = cneg(d, p, base);
        cadd(d, p, x_j, nb) // (base + term) + (-base)
    };
    let diff_eq = cancel_add_neg_right(d, p, base, term); // Equiv diff term

    let neg_term_le_delta = neg_le_of_nonneg(d, p, term, delta, term_nonneg, delta_nonneg);
    let abs_term_le_delta = d.lemma(p.abs_le, &[term, delta, term_le_delta, neg_term_le_delta]);

    let abs_diff = d.const_app(p.abs, &[diff]);
    let abs_term = d.const_app(p.abs, &[term]);
    let abs_diff_term = d.lemma(p.abs_congr, &[diff, term, diff_eq]); // Equiv abs_diff abs_term
    let abs_term_diff = d.lemma(p.equiv_symm, &[abs_diff, abs_term, abs_diff_term]);
    let refl_delta = d.lemma(p.equiv_refl, &[delta]);
    d.lemma(
        p.le_congr,
        &[
            abs_term,
            abs_diff,
            delta,
            delta,
            abs_term_diff,
            refl_delta,
            abs_term_le_delta,
        ],
    )
    // : le abs_diff delta
}

/// `Equiv (sample_point x0 step (Nat.succ i)) (add (sample_point x0 step i)
/// step)` — the coarse/fine successor step `x_{i+1} ~ x_i + step`, in
/// ADDITIVE form. A restatement of `monotone.rs`'s private
/// `consecutive_diff_eq_step` (which proves the DIFFERENCE form `x_{i+1} −
/// x_i ~ step`, built for a different call site) built directly to the
/// additive shape [`declare_fine_sample_in_bounds`] needs: duplicated rather
/// than imported, since that file is out of scope for edits in this slice
/// and `consecutive_diff_eq_step` is private there.
///
/// Route: `ofNat (succ i) ~ ofNat i + one` ([`of_nat_succ_equiv_local`]),
/// `mul_congr` to lift that into `(ofNat (succ i))·step ~ (ofNat i +
/// one)·step`, [`right_distrib`] to expand the right side to `(ofNat
/// i)·step + one·step`, `mul_one`/`mul_comm` to fold `one·step ~ step`, then
/// `add_congr` with `x0` and `add_assoc` to re-bracket `x0 + ((ofNat
/// i)·step + step)` as `(x0 + (ofNat i)·step) + step`.
fn sample_point_succ_step(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x0: ExprId,
    step: ExprId,
    i: ExprId,
) -> ExprId {
    let of_nat_i = d.const_app(p.of_nat, &[i]);
    let u = cmul(d, p, of_nat_i, step);
    let x_i = cadd(d, p, x0, u); // sample_point x0 step i

    let si = d.succ(i);
    let of_nat_si = d.const_app(p.of_nat, &[si]);
    let v = cmul(d, p, of_nat_si, step); // ofNat(succ i) * step
    let x_si = cadd(d, p, x0, v); // sample_point x0 step (succ i)

    // v_eq_u_plus_step : Equiv v (add u step).
    let v_eq_u_plus_step = {
        let one_c = d.kernel().const_(p.one, vec![]);
        let succ_eq = of_nat_succ_equiv_local(d, p, i); // Equiv of_nat_si (add of_nat_i one_c)
        let sum_of_nat = cadd(d, p, of_nat_i, one_c);
        let expanded = cmul(d, p, sum_of_nat, step);
        let h_a = {
            let refl_step = d.lemma(p.equiv_refl, &[step]);
            d.lemma(
                p.mul_congr,
                &[of_nat_si, sum_of_nat, step, step, succ_eq, refl_step],
            )
        };
        let h_b = right_distrib(d, p, of_nat_i, one_c, step);
        let one_step = cmul(d, p, one_c, step);
        let distributed = cadd(d, p, u, one_step);
        let h_c = {
            let refl_u = d.lemma(p.equiv_refl, &[u]);
            let one_mul_step = {
                let step_one = cmul(d, p, step, one_c);
                let mul_one_step = d.lemma(p.mul_one, &[step]);
                let comm = d.lemma(p.mul_comm, &[one_c, step]);
                d.lemma(
                    p.equiv_trans,
                    &[one_step, step_one, step, comm, mul_one_step],
                )
            };
            d.lemma(p.add_congr, &[u, u, one_step, step, refl_u, one_mul_step])
        };
        let u_plus_step = cadd(d, p, u, step);
        let s1 = d.lemma(p.equiv_trans, &[v, expanded, distributed, h_a, h_b]);
        d.lemma(p.equiv_trans, &[v, distributed, u_plus_step, s1, h_c])
    };

    // x_si = x0 + v ~ x0 + (u + step) ~ (x0 + u) + step = x_i + step.
    let u_plus_step = cadd(d, p, u, step);
    let x0_u_step = cadd(d, p, x0, u_plus_step);
    let h_v = {
        let refl_x0 = d.lemma(p.equiv_refl, &[x0]);
        d.lemma(
            p.add_congr,
            &[x0, x0, v, u_plus_step, refl_x0, v_eq_u_plus_step],
        )
    };
    let x_i_step = cadd(d, p, x_i, step);
    let h_assoc = {
        // add_assoc(x0, u, step) : Equiv (add (add x0 u) step) (add x0 (add u step))
        //                        = Equiv x_i_step x0_u_step
        let assoc = d.lemma(p.add_assoc, &[x0, u, step]);
        d.lemma(p.equiv_symm, &[x_i_step, x0_u_step, assoc])
    };
    d.lemma(p.equiv_trans, &[x_si, x0_u_step, x_i_step, h_v, h_assoc])
    // : Equiv x_si x_i_step
}

/// `CReal.fineSample_in_bounds : ∀ a b m n i j, le a b → Nat.le i m →
/// Nat.lt j (Nat.succ n) → And (le a x) (le x b)`, `x := add (sample_point a
/// delta_m i) (mul (ofNat j) delta_fine)`, `delta_m := mul (add b (neg a))
/// (embed (Rat.natDivSucc 1 m))`, `delta_fine := mul delta_m (embed
/// (Rat.natDivSucc 1 n))` — the fine-sample placement lemma
/// `riemannSum_cauchy`'s per-block fold needs: every FINE sample point `x`
/// inside COARSE block `i` (`i ≤ m`) lies in `[a, b]`, for every fine
/// sub-index `j < Nat.succ n`. See the module documentation's "the succ-shape
/// bridge" section header and [`CRealPrelude::fine_sample_in_bounds`]'s own
/// doc comment for why this is the one-index-shift generalization
/// `riemannSum_sample_in_bounds`/`subdivisionPoint_in_bounds` do not cover.
///
/// Route: two calls to `subdivisionPoint_in_bounds`, at coarse indices `i`
/// (giving `a ≤ base`, `base := sample_point a delta_m i`) and `Nat.succ i`
/// (giving `base' ≤ b`, `base' := sample_point a delta_m (Nat.succ i)`),
/// bracketing the block `[base, base + delta_m]` via
/// [`sample_point_succ_step`] (`base' ~ base + delta_m`). `i ≤ m` weakens to
/// both `i ≤ succ m` (`Nat.le_trans` against `Nat.le_succ`, the exact idiom
/// [`nat_le_of_lt`] already uses) and `succ i ≤ succ m` (`Nat.succ_le_succ`
/// directly) — the two hypotheses `subdivisionPoint_in_bounds` needs at
/// those two indices. [`fine_term_and_bounds`] gives the fine term's own
/// `0 ≤ term` (lower: [`shift_le_of_nonneg`] places `x` past `base`) and
/// `term ≤ delta_m` (upper: `add_le_add` places `x` before `base'`, then
/// `le_congr` rewrites `base'` down to `base + delta_m`); `le_trans` on each
/// side closes `a ≤ x` and `x ≤ b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_fine_sample_in_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let logic = p.rat.int.logic;

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let hi_ty = d.le(i, m); // Nat.le i m
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let sn = d.succ(n);
    let hj_ty = d.lt(j, sn); // Nat.lt j (Nat.succ n)
    let hj_fv = d.fresh_fvar();
    let hj = d.kernel().fvar(hj_fv);

    let (delta_m, delta_m_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let base = sample_point(d, p, a, delta_m, i);
    let (term, term_nonneg, term_le_delta_m) =
        fine_term_and_bounds(d, p, delta_m, n, j, hj, delta_m_nonneg);
    let x = cadd(d, p, base, term); // the fine sample point

    let np = d.prelude();
    let succ_m = d.succ(m);

    // lower : le a x.
    let a_le_x = {
        // hle_i_succm : Nat.le i (Nat.succ m), from `i ≤ m` and `m ≤ succ m`.
        let hle_i_succm = {
            let le_succ_m = d.const_app(np.le_succ, &[m]);
            d.const_app(np.le_trans, &[i, m, succ_m, hi, le_succ_m])
        };
        let and_base = d.const_app(
            p.subdivision_point_in_bounds,
            &[a, b, m, i, hab, hle_i_succm],
        );
        let a_le_base_ty = cle(d, p, a, base);
        let base_le_b_ty = cle(d, p, base, b);
        let a_le_base = d.const_app(logic.and_left, &[a_le_base_ty, base_le_b_ty, and_base]);

        let base_le_x = shift_le_of_nonneg(d, p, base, term, term_nonneg);
        d.lemma(p.le_trans, &[a, base, x, a_le_base, base_le_x])
    };

    // upper : le x b.
    let x_le_b = {
        let succ_i = d.succ(i);
        // hle_si_succm : Nat.le (Nat.succ i) (Nat.succ m), from `i ≤ m`.
        let hle_si_succm = d.const_app(np.succ_le_succ, &[i, m, hi]);
        let and_base_succ = d.const_app(
            p.subdivision_point_in_bounds,
            &[a, b, m, succ_i, hab, hle_si_succm],
        );
        let base_succ = sample_point(d, p, a, delta_m, succ_i);
        let a_le_base_succ_ty = cle(d, p, a, base_succ);
        let base_succ_le_b_ty = cle(d, p, base_succ, b);
        let base_succ_le_b = d.const_app(
            logic.and_right,
            &[a_le_base_succ_ty, base_succ_le_b_ty, and_base_succ],
        );

        // base_succ ~ add base delta_m.
        let succ_step_eq = sample_point_succ_step(d, p, a, delta_m, i);
        let base_plus_delta = cadd(d, p, base, delta_m);
        let refl_b = d.lemma(p.equiv_refl, &[b]);
        let base_plus_delta_le_b = d.lemma(
            p.le_congr,
            &[
                base_succ,
                base_plus_delta,
                b,
                b,
                succ_step_eq,
                refl_b,
                base_succ_le_b,
            ],
        );

        // x = add base term ≤ add base delta_m, from term ≤ delta_m.
        let refl_base = d.lemma(p.le_refl, &[base]);
        let x_le_base_plus_delta = d.lemma(
            p.add_le_add,
            &[base, base, term, delta_m, refl_base, term_le_delta_m],
        );
        d.lemma(
            p.le_trans,
            &[
                x,
                base_plus_delta,
                b,
                x_le_base_plus_delta,
                base_plus_delta_le_b,
            ],
        )
    };

    let a_le_x_ty = cle(d, p, a, x);
    let x_le_b_ty = cle(d, p, x, b);
    let and_ty = d.const_app(logic.and, &[a_le_x_ty, x_le_b_ty]);
    let proof_body = and_intro(d, p, a_le_x_ty, x_le_b_ty, a_le_x, x_le_b);

    let ty = {
        let after_hj = d.arrow(hj_ty, and_ty);
        let after_hi = d.arrow(hi_ty, after_hj);
        let after_hab = d.arrow(hab_ty, after_hi);
        let over_j = d.pi_fv(j_fv, nat, after_hab);
        let over_i = d.pi_fv(i_fv, nat, over_j);
        let over_n = d.pi_fv(n_fv, nat, over_i);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let with_hj = d.lam_fv(hj_fv, hj_ty, proof_body);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hi);
        let over_j = d.lam_fv(j_fv, nat, with_hab);
        let over_i = d.lam_fv(i_fv, nat, over_j);
        let over_n = d.lam_fv(n_fv, nat, over_i);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        d.lam_fv(a_fv, carrier, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.fine_sample_in_bounds,
        uparams: vec![],
        ty,
        value,
    })
}

// --- roadmap step 2: the per-block bound, via `UniformlyContinuousOn.spec` -

/// `CReal.close (x y : CReal) (q : Rat) : Prop := le (abs (add x (neg y)))
/// (ofRat q)` — `|x − y| ≤ q`, real-valued and index-free in `x, y`.
/// Reproduced from `uniform_continuity.rs`'s private `close_within` (that
/// file is out of scope for edits in this slice): the exact shape
/// `UniformlyContinuousOn.spec`'s hypothesis and conclusion both take.
fn close_within(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, q: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny);
    let magnitude = d.const_app(p.abs, &[diff]);
    let target = embed(d, p, q);
    cle(d, p, magnitude, target)
}

/// `CReal.fineSample_close : ∀ F a b e m n i j, le a b →
/// UniformlyContinuousOn F a b → Nat.le i m → Nat.lt j (Nat.succ n) →
/// Nat.le deep m → close_within (F fine_j) (F base_i) (Rat.natDivSucc 1 e)`,
/// `deep := (Nat.succ (bound (add b (neg a))))·(modulus F a b u e) + bound
/// (add b (neg a))`, `base_i := sample_point a delta_m i`, `fine_j := add
/// base_i (mul (ofNat j) (mul delta_m (embed (natDivSucc 1 n))))`, `delta_m
/// := mul (add b (neg a)) (embed (natDivSucc 1 m))` — roadmap step 2, and
/// this module's own documentation's success condition on its own: EVERY
/// fine sample point inside coarse block `i` is within `1/(e+1)` of that
/// block's own coarse value `F(base_i)`, once the coarse block count `m` is
/// Archimedean-large enough relative to the modulus of uniform continuity
/// at target precision `e`.
///
/// Route: [`sample_offset_bound`] bounds the fine sample's OFFSET from
/// `base_i` by `delta_m` exactly; [`declare_mesh_le_of_ge`]'s own theorem
/// (at `outer := modulus F a b u e`) rescales `delta_m` down to `natDivSucc
/// 1 outer` PROVIDED `m` clears the Archimedean threshold `deep`;
/// `le_trans` chains the two into exactly `UniformlyContinuousOn.spec`'s
/// own hypothesis shape at `n := e`. The two domain-membership pairs `spec`
/// needs come from [`declare_fine_sample_in_bounds`] (the fine point) and
/// [`declare_riemann_sample_in_bounds`] (the coarse point, its `Nat.lt i
/// (Nat.succ m)` hypothesis obtained from this theorem's own `Nat.le i m`
/// via `Nat.lt_succ_of_le`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_fine_sample_close(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let hi_ty = d.le(i, m);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let sn = d.succ(n);
    let hj_ty = d.lt(j, sn);
    let hj_fv = d.fresh_fvar();
    let hj = d.kernel().fvar(hj_fv);

    // outer := UniformlyContinuousOn.modulus F a b u e.
    let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let outer = d.apply(modulus_fn, &[e]);

    // deep, the same Archimedean threshold `mesh_le_of_ge` computes
    // internally at this `outer`.
    let width = width_of(d, p, a, b);
    let (c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);
    let me = NatOps::mul(d, magnitude, outer);
    let deep = NatOps::add(d, me, c);
    let hge_ty = d.le(deep, m);
    let hge_fv = d.fresh_fvar();
    let hge = d.kernel().fvar(hge_fv);

    let (delta_m, delta_m_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let base_i = sample_point(d, p, a, delta_m, i);
    let (term, _term_nonneg, _term_le_delta_m) =
        fine_term_and_bounds(d, p, delta_m, n, j, hj, delta_m_nonneg);
    let fine_j = cadd(d, p, base_i, term);

    // hax, hxb : le a fine_j, le fine_j b.
    let (hax, hxb) = {
        let and_fine = d.const_app(p.fine_sample_in_bounds, &[a, b, m, n, i, j, hab, hi, hj]);
        let hax_ty = cle(d, p, a, fine_j);
        let hxb_ty = cle(d, p, fine_j, b);
        let hax = d.const_app(logic.and_left, &[hax_ty, hxb_ty, and_fine]);
        let hxb = d.const_app(logic.and_right, &[hax_ty, hxb_ty, and_fine]);
        (hax, hxb)
    };

    // hay, hyb : le a base_i, le base_i b.
    let (hay, hyb) = {
        let np = d.prelude();
        let hi_lt = d.const_app(np.lt_succ_of_le, &[i, m, hi]); // Nat.lt i (Nat.succ m)
        let and_coarse = d.const_app(p.riemann_sample_in_bounds, &[a, b, m, i, hab, hi_lt]);
        let hay_ty = cle(d, p, a, base_i);
        let hyb_ty = cle(d, p, base_i, b);
        let hay = d.const_app(logic.and_left, &[hay_ty, hyb_ty, and_coarse]);
        let hyb = d.const_app(logic.and_right, &[hay_ty, hyb_ty, and_coarse]);
        (hay, hyb)
    };

    // hclose : close_within fine_j base_i (natDivSucc 1 outer).
    let hclose = {
        let offset_bound = sample_offset_bound(d, p, base_i, delta_m, n, j, hj, delta_m_nonneg);
        // offset_bound : le (abs (add fine_j (neg base_i))) delta_m
        let mesh_bound = d.const_app(p.mesh_le_of_ge, &[a, b, outer, m, hab, hge]);
        // mesh_bound : le delta_m (embed (natDivSucc 1 outer))
        let one_nat = d.num(1);
        let out_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, outer]);
        let out_bound = embed(d, p, out_rat);
        let ny = cneg(d, p, base_i);
        let diff = cadd(d, p, fine_j, ny);
        let abs_diff = d.const_app(p.abs, &[diff]);
        d.lemma(
            p.le_trans,
            &[abs_diff, delta_m, out_bound, offset_bound, mesh_bound],
        )
    };

    let conclusion = {
        let fx = d.apply(f, &[fine_j]);
        let fy = d.apply(f, &[base_i]);
        let one_nat = d.num(1);
        let out_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
        close_within(d, p, fx, fy, out_rat)
    };

    let proof_body = d.const_app(
        p.uc_spec,
        &[f, a, b, u, e, fine_j, base_i, hax, hxb, hay, hyb, hclose],
    );

    let ty = {
        let after_hge = d.arrow(hge_ty, conclusion);
        let after_hj = d.arrow(hj_ty, after_hge);
        let after_hi = d.arrow(hi_ty, after_hj);
        // `u` (dependent, not `arrow`): `after_hi` mentions the fvar `u`
        // through `hge_ty`'s own `deep`/`outer := modulus F a b u e`.
        let after_u = d.pi_fv(u_fv, u_ty, after_hi);
        let after_hab = d.arrow(hab_ty, after_u);
        let over_j = d.pi_fv(j_fv, nat, after_hab);
        let over_i = d.pi_fv(i_fv, nat, over_j);
        let over_n = d.pi_fv(n_fv, nat, over_i);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_e = d.pi_fv(e_fv, nat, over_m);
        let over_b = d.pi_fv(b_fv, carrier, over_e);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_hge = d.lam_fv(hge_fv, hge_ty, proof_body);
        let with_hj = d.lam_fv(hj_fv, hj_ty, with_hge);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let with_u = d.lam_fv(u_fv, u_ty, with_hi);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_j = d.lam_fv(j_fv, nat, with_hab);
        let over_i = d.lam_fv(i_fv, nat, over_j);
        let over_n = d.lam_fv(n_fv, nat, over_i);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_e = d.lam_fv(e_fv, nat, over_m);
        let over_b = d.lam_fv(b_fv, carrier, over_e);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.fine_sample_close,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod succ_shape_bridge_tests {
    use super::*;
    use crate::Declaration;

    /// Wraps [`succ_mul_succ`] at symbolic `n, m` in a throwaway anonymous
    /// theorem and lets the kernel accept or reject it — building the Rust
    /// closures is not evidence the *term* is well-typed, only
    /// `Kernel::add_declaration`'s trusted checker is (the same idiom as
    /// `sqrt.rs`'s `bridging_smoke_tests`).
    #[test]
    fn succ_mul_succ_type_checks_symbolically() {
        crate::on_a_deep_stack(succ_mul_succ_type_checks_symbolically_body);
    }

    fn succ_mul_succ_type_checks_symbolically_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);

        let (m_prime, proof) = succ_mul_succ(&mut d, n, m);

        let sn = d.succ(n);
        let sm = d.succ(m);
        let lhs = NatOps::mul(&mut d, sn, sm);
        let succ_m_prime = d.succ(m_prime);
        let claim = d.eq(lhs, succ_m_prime);

        let value = {
            let with_m = d.lam_fv(m_fv, nat, proof);
            d.lam_fv(n_fv, nat, with_m)
        };
        let ty = {
            let over_m = d.pi_fv(m_fv, nat, claim);
            d.pi_fv(n_fv, nat, over_m)
        };

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "succShapeBridgeSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "succ_mul_succ must type-check: {:?}",
            result.err()
        );
    }

    /// The mandatory concrete instantiation `n = 2, m = 3` (`n != m`, per the
    /// task's own caution that a transposed-argument defect is invisible at
    /// `n = m`): `3 * 4 = 12 = succ 11`, `m_prime = 6 + 2 + 3 = 11`. Checked
    /// by `Eq.refl` against the literals `11`/`12` — the kernel's own
    /// reduction, not a comment, is what "reduces" means here.
    #[test]
    fn succ_mul_succ_reduces_at_two_three() {
        crate::on_a_deep_stack(succ_mul_succ_reduces_at_two_three_body);
    }

    fn succ_mul_succ_reduces_at_two_three_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let n = d.num(2);
        let m = d.num(3);
        let (m_prime, _proof) = succ_mul_succ(&mut d, n, m);

        // m_prime must independently equal the literal 11 (n*m+n+m = 6+2+3).
        let eleven = d.num(11);
        let m_prime_eq_eleven = d.eq(m_prime, eleven);
        let m_prime_refl = d.refl(eleven);

        let twelve = d.num(12);
        let succ_m_prime = d.succ(m_prime);
        let succ_m_prime_eq_twelve = d.eq(succ_m_prime, twelve);
        let succ_m_prime_refl = d.refl(twelve);

        let anon = d.kernel().anon();
        let name1 = d
            .kernel()
            .name_str(anon, "succShapeBridgeSmokeMPrimeEleven");
        let r1 = d.kernel().add_declaration(Declaration::Theorem {
            name: name1,
            uparams: vec![],
            ty: m_prime_eq_eleven,
            value: m_prime_refl,
        });
        assert!(r1.is_ok(), "m_prime must reduce to 11: {:?}", r1.err());

        let name2 = d
            .kernel()
            .name_str(anon, "succShapeBridgeSmokeSuccMPrimeTwelve");
        let r2 = d.kernel().add_declaration(Declaration::Theorem {
            name: name2,
            uparams: vec![],
            ty: succ_m_prime_eq_twelve,
            value: succ_m_prime_refl,
        });
        assert!(r2.is_ok(), "succ m_prime must reduce to 12: {:?}", r2.err());
    }
}

// --- the common-refinement construction -- comparing two ARBITRARY,
// otherwise-unrelated subinterval counts, not a count against its own
// refinement. -----------------------------------------------------------
//
// [`declare_riemann_sum_cauchy`]'s own module placement comment (and
// [`declare_shared_index_to_canonical`]'s doc comment) name the exact gap
// this closes: `riemannSum_cauchy` only ever compares a count `m` to ONE
// `succ_mul_succ`-refinement of itself (`m` and `(n+1)(m+1)-1` for a chosen
// refinement factor `n`). Neither it nor `sharedIndexToCanonical` says
// anything about two counts `m1, m2` with no such relationship. This
// section is that bridge, standalone and `riemannSum`-independent (pure
// `Nat` arithmetic, reusable anywhere a common refinement of two counts is
// needed).

/// `(base + k) + m = (base + m) + k` — the additive reassociation
/// [`common_refinement`] needs to reorder a trailing `+m2+m1`/`+m1+m2` once
/// [`succ_mul_succ`]'s own multiplicative commutation has already lined up
/// the leading product. A verbatim re-derivation of `nat_prelude/euler.rs`'s
/// private `swap_tail` (Rust-private there; `creal` cannot see it, and that
/// crate's own module boundary is out of this slice's scope per the task
/// briefing — see [`succ_mul_succ`]'s own doc comment for the identical
/// call this file already makes on a `nat_prelude` name it CAN see): two
/// `Nat.add_assoc` steps around one `Nat.add_comm` in the middle.
fn nat_add_swap_tail(d: &mut IntDev<'_>, base: ExprId, k: ExprId, m: ExprId) -> ExprId {
    let np = d.prelude();
    let bk = NatOps::add(d, base, k);
    let start = NatOps::add(d, bk, m);
    let km = NatOps::add(d, k, m);
    let mid1 = NatOps::add(d, base, km);
    let assoc1 = d.lemma(np.add_assoc, &[base, k, m]); // Eq start mid1
    let mk = NatOps::add(d, m, k);
    let mid2 = NatOps::add(d, base, mk);
    let commute = d.lemma(np.add_comm, &[k, m]); // Eq km mk
    let step2 = NatOps::congr(d, km, mk, commute, &|d, t| NatOps::add(d, base, t)); // Eq mid1 mid2
    let bm = NatOps::add(d, base, m);
    let target = NatOps::add(d, bm, k);
    let assoc2 = d.lemma(np.add_assoc, &[base, m, k]); // Eq target mid2
    let step3 = NatOps::symm(d, target, mid2, assoc2); // Eq mid2 target
    let (_, proof) = NatOps::chain(d, start, &[(mid1, assoc1), (mid2, step2), (target, step3)]);
    proof
}

/// The common-refinement construction: given two arbitrary `Nat` counts
/// `m1, m2` with no assumed relationship, produces a SINGLE `Nat` `l` that
/// is [`succ_mul_succ`]'s own refinement target from BOTH directions —
/// directly, `succ l = (succ m2)*(succ m1)` (refining `m1` by factor `m2`),
/// and, after rewriting through the returned equality, `succ l = (succ
/// m1)*(succ m2)` (refining `m2` by factor `m1`) as well.
///
/// Two [`succ_mul_succ`] calls give `l := ((m2*m1)+m2)+m1` and `l2 :=
/// ((m1*m2)+m1)+m2`. These are not the same term syntactically, but are
/// propositionally equal: `Nat.mul_comm` identifies the leading products
/// (`m2*m1 = m1*m2`), then [`nat_add_swap_tail`] reorders the trailing
/// `+m2+m1` into `+m1+m2` once the leading terms agree.
///
/// **The `Nat.mul_comm` step is load-bearing only at SYMBOLIC `m1, m2`.** At
/// any CONCRETE literal pair, `Nat.mul`/`Nat.add` already reduce both `l`
/// and `l2` to the identical numeral by pure computation, so a construction
/// that dropped the commutation (or reassociated wrongly) would be
/// INVISIBLE there — a concrete instantiation cannot exercise this bug,
/// only a symbolic one can (see this declaration's own test module, which
/// checks both, plus a genuine negative control at the proof-term level
/// rather than the value level for exactly this reason).
///
/// Returns `(l, l2, l2_eq_l)`: `l2_eq_l : Eq Nat l2 l`, oriented so a caller
/// holding a fact about `l2` (from the SECOND [`succ_mul_succ`] call) can
/// [`nat_rewrite_prop`](crate::rat_prelude::ops::nat_rewrite_prop) it onto
/// `l` — the target the FIRST call already lands on directly, with no
/// rewrite needed on that side.
fn common_refinement(d: &mut IntDev<'_>, m1: ExprId, m2: ExprId) -> (ExprId, ExprId, ExprId) {
    let (l, _sm2_sm1_eq) = succ_mul_succ(d, m2, m1); // l  = ((m2*m1)+m2)+m1
    let (l2, _sm1_sm2_eq) = succ_mul_succ(d, m1, m2); // l2 = ((m1*m2)+m1)+m2

    let x1 = NatOps::mul(d, m2, m1);
    let x2 = NatOps::mul(d, m1, m2);
    let np = d.prelude();
    let comm_mul = d.lemma(np.mul_comm, &[m2, m1]); // Eq x1 x2

    // Eq l l1_prime, l1_prime := (x2+m2)+m1, via congruence on comm_mul in
    // the one-hole context `fun t => (t+m2)+m1`.
    let l1_prime = {
        let t = NatOps::add(d, x2, m2);
        NatOps::add(d, t, m1)
    };
    let congr_step = NatOps::congr(d, x1, x2, comm_mul, &|d, t| {
        let inner = NatOps::add(d, t, m2);
        NatOps::add(d, inner, m1)
    });

    // Eq l1_prime l2, via `nat_add_swap_tail` at base := x2, k := m2, m := m1:
    // (x2+m2)+m1 = (x2+m1)+m2 = l2.
    let swap = nat_add_swap_tail(d, x2, m2, m1);

    let (_, l_eq_l2) = NatOps::chain(d, l, &[(l1_prime, congr_step), (l2, swap)]);
    let l2_eq_l = NatOps::symm(d, l, l2, l_eq_l2);

    (l, l2, l2_eq_l)
}

#[cfg(test)]
mod common_refinement_tests {
    use super::*;
    use crate::Declaration;

    /// **The load-bearing check.** [`common_refinement`] at SYMBOLIC `m1,
    /// m2` (free variables, so `Nat.mul`/`Nat.add` cannot simply compute the
    /// answer out from under the proof) — wraps the produced `Eq Nat l2 l`
    /// in a throwaway anonymous theorem and lets the kernel accept or
    /// reject it, the same idiom [`succ_shape_bridge_tests`] already uses
    /// for [`succ_mul_succ`] one section up.
    #[test]
    fn common_refinement_type_checks_symbolically() {
        crate::on_a_deep_stack(common_refinement_type_checks_symbolically_body);
    }

    fn common_refinement_type_checks_symbolically_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();

        let m1_fv = d.fresh_fvar();
        let m1 = d.kernel().fvar(m1_fv);
        let m2_fv = d.fresh_fvar();
        let m2 = d.kernel().fvar(m2_fv);

        let (l, l2, l2_eq_l) = common_refinement(&mut d, m1, m2);
        let claim = d.eq(l2, l);

        let value = {
            let with_m2 = d.lam_fv(m2_fv, nat, l2_eq_l);
            d.lam_fv(m1_fv, nat, with_m2)
        };
        let ty = {
            let over_m2 = d.pi_fv(m2_fv, nat, claim);
            d.pi_fv(m1_fv, nat, over_m2)
        };

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "commonRefinementSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "common_refinement must type-check at symbolic m1, m2: {:?}",
            result.err()
        );
    }

    /// The mandatory concrete instantiation `m1 = 2, m2 = 3` (`m1 != m2`,
    /// the same caution [`succ_shape_bridge_tests`] applies to
    /// [`succ_mul_succ`] itself: a transposed-argument defect is invisible
    /// at `m1 = m2`). `l = ((3*2)+3)+2 = 11`, `l2 = ((2*3)+2)+3 = 11` — both
    /// reduce to the SAME literal by pure computation (confirmed
    /// independently by `Eq.refl` below), which is exactly why the
    /// SYMBOLIC test above, not this one, is the one that actually
    /// exercises `Nat.mul_comm`/[`nat_add_swap_tail`].
    #[test]
    fn common_refinement_reduces_at_two_three() {
        crate::on_a_deep_stack(common_refinement_reduces_at_two_three_body);
    }

    fn common_refinement_reduces_at_two_three_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let m1 = d.num(2);
        let m2 = d.num(3);
        let (l, l2, l2_eq_l) = common_refinement(&mut d, m1, m2);

        let eleven = d.num(11);
        let l_eq_eleven = d.eq(l, eleven);
        let l_refl = d.refl(eleven);
        let anon = d.kernel().anon();
        let name1 = d.kernel().name_str(anon, "commonRefinementSmokeLEleven");
        let r1 = d.kernel().add_declaration(Declaration::Theorem {
            name: name1,
            uparams: vec![],
            ty: l_eq_eleven,
            value: l_refl,
        });
        assert!(r1.is_ok(), "l must reduce to 11: {:?}", r1.err());

        let l2_eq_eleven = d.eq(l2, eleven);
        let l2_refl = d.refl(eleven);
        let name2 = d.kernel().name_str(anon, "commonRefinementSmokeL2Eleven");
        let r2 = d.kernel().add_declaration(Declaration::Theorem {
            name: name2,
            uparams: vec![],
            ty: l2_eq_eleven,
            value: l2_refl,
        });
        assert!(r2.is_ok(), "l2 must reduce to 11: {:?}", r2.err());

        // The composed proof also checks concretely (sanity, not the main
        // point -- see the symbolic test above).
        let claim = d.eq(l2, l);
        let name3 = d.kernel().name_str(anon, "commonRefinementSmokeConcrete");
        let r3 = d.kernel().add_declaration(Declaration::Theorem {
            name: name3,
            uparams: vec![],
            ty: claim,
            value: l2_eq_l,
        });
        assert!(
            r3.is_ok(),
            "common_refinement's composed proof must also check concretely: {:?}",
            r3.err()
        );
    }

    /// **Negative control, at the proof-term level rather than the value
    /// level** (a value-level control is unavailable here -- see
    /// [`common_refinement`]'s own doc comment for why any concrete
    /// literal pair makes `l` and `l2` compute to the same numeral
    /// regardless of whether the construction is right). Reuses the EXACT
    /// SAME proof term `l2_eq_l` — built once, not re-derived — against the
    /// off-by-one type `Eq Nat l2 (succ l)`. That statement is genuinely
    /// FALSE (a successor is never equal to its own predecessor's value:
    /// concretely `11 != 12`), not vacuous and not accidentally true, so
    /// the kernel must refuse it.
    #[test]
    fn common_refinement_proof_rejected_at_wrong_type() {
        crate::on_a_deep_stack(common_refinement_proof_rejected_at_wrong_type_body);
    }

    fn common_refinement_proof_rejected_at_wrong_type_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let m1 = d.num(2);
        let m2 = d.num(3);
        let (l, _l2, l2_eq_l) = common_refinement(&mut d, m1, m2);
        let succ_l = d.succ(l);
        // `_l2` is deliberately underscore-prefixed by `common_refinement`'s
        // own destructured return shape; this test intentionally uses it to
        // build a wrong-typed theorem, not a naming oversight.
        #[allow(clippy::used_underscore_binding)]
        let wrong = d.eq(_l2, succ_l);

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "commonRefinementSmokeWrong");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: wrong,
            value: l2_eq_l,
        });
        assert!(
            result.is_err(),
            "the l2_eq_l proof must be REFUSED against the off-by-one type Eq Nat l2 (succ l)"
        );
    }
}

// --- the THREE-way common refinement -- `integral_add`'s own gap, per this
// file's module documentation's 2026-08-26 entry: `riemannSum_add`'s exact
// per-`m` identity only fires when the FG/F/G mesh counts already agree, so
// bridging `riemannSum (F+G)` at ITS OWN mesh to `riemannSum F` and
// `riemannSum G` at THEIR OWN (generally different) meshes needs a single
// shared refinement `L` of all THREE counts at once, not two. -------------

/// `Eq Nat (mul (succ n) (succ m)) (succ (succ_mul_succ n m).0)` --
/// [`succ_mul_succ`]'s own SECOND return value, restated at this exact type.
/// Valid via the identical pure ι-reduction
/// [`declare_mesh_reciprocal_mul`]'s own module documentation confirms for
/// `Nat.add (Nat.mul n (Nat.succ m)) (Nat.succ m)`: with `m` (not `succ n`)
/// as `Nat.mul`'s left argument, `Nat.succ_mul`'s stated right-hand side
/// unfolds the rest of the way to `succ ((n·m+n)+m)` by pure defeq, so the
/// SAME proof term [`succ_mul_succ`] already builds checks at this
/// stronger, succ-headed type with no further rewrite -- nothing here
/// re-derives anything; it just names the fact for [`three_way_swap`].
fn succ_mul_succ_eq(d: &mut IntDev<'_>, n: ExprId, m: ExprId) -> ExprId {
    succ_mul_succ(d, n, m).1
}

/// `Eq Nat (succ_mul_succ (succ_mul_succ a b).0 c).0 (succ_mul_succ
/// (succ_mul_succ a c).0 b).0` -- writing `l(x,y) := succ_mul_succ(x,y).0`,
/// this is `l (l a b) c = l (l a c) b`: refining `a` by `b` and the result
/// by `c` reaches the SAME count as refining `a` by `c` and the result by
/// `b`. [`common_refinement3`]'s "outer-swap" move, needed to reach a THIRD
/// count from a refinement already built from the first two, which
/// [`common_refinement`]'s own two-count route (`Nat.mul_comm` plus
/// [`nat_add_swap_tail`] on the literal `l`-formula) does not reach.
///
/// Proved differently from [`common_refinement`]'s own route: rather than
/// manipulating the flattened `l`-formula, this composes two
/// [`succ_mul_succ_eq`] facts into `Eq Nat (mul (mul (succ a) (succ b))
/// (succ c)) (succ (l (l a b) c))` and its mirror for `(a, c, b)`, bridges
/// the two three-factor PRODUCTS via `Nat.mul_assoc`/`Nat.mul_comm` (the
/// standard "`mul_right_comm`": `(x·y)·z = (x·z)·y`), and strips the shared
/// outer `Nat.succ` via `Nat.succ_injective` — the only place in this
/// development that needs Nat.succ injectivity rather than raw
/// `Nat.add`/`Nat.mul` congruence.
fn three_way_swap(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let np = d.prelude();
    let sa = d.succ(a);
    let sb = d.succ(b);
    let sc = d.succ(c);
    let sasb = NatOps::mul(d, sa, sb);
    let sasbsc = NatOps::mul(d, sasb, sc);
    let sasc = NatOps::mul(d, sa, sc);
    let sascsb = NatOps::mul(d, sasc, sb);

    // EQ_LHS : Eq Nat (mul (mul sa sb) sc) (succ l_ab_c),  l_ab_c = l(l(a,b),c).
    let (l_ab, _) = succ_mul_succ(d, a, b);
    let eq_ab = succ_mul_succ_eq(d, a, b); // Eq (mul sa sb) (succ l_ab)
    let (l_ab_c, _) = succ_mul_succ(d, l_ab, c);
    let eq_ab_c = succ_mul_succ_eq(d, l_ab, c); // Eq (mul (succ l_ab) sc) (succ l_ab_c)
    let succ_l_ab = d.succ(l_ab);
    let succ_l_ab_sc = NatOps::mul(d, succ_l_ab, sc);
    let step_lhs = NatOps::congr(d, sasb, succ_l_ab, eq_ab, &|d, t| NatOps::mul(d, t, sc));
    let succ_l_ab_c = d.succ(l_ab_c);
    let (_, eq_lhs) = NatOps::chain(
        d,
        sasbsc,
        &[(succ_l_ab_sc, step_lhs), (succ_l_ab_c, eq_ab_c)],
    );

    // EQ_RHS : Eq Nat (mul (mul sa sc) sb) (succ l_ac_b),  l_ac_b = l(l(a,c),b).
    let (l_ac, _) = succ_mul_succ(d, a, c);
    let eq_ac = succ_mul_succ_eq(d, a, c);
    let (l_ac_b, _) = succ_mul_succ(d, l_ac, b);
    let eq_ac_b = succ_mul_succ_eq(d, l_ac, b);
    let succ_l_ac = d.succ(l_ac);
    let succ_l_ac_sb = NatOps::mul(d, succ_l_ac, sb);
    let step_rhs = NatOps::congr(d, sasc, succ_l_ac, eq_ac, &|d, t| NatOps::mul(d, t, sb));
    let succ_l_ac_b = d.succ(l_ac_b);
    let (_, eq_rhs) = NatOps::chain(
        d,
        sascsb,
        &[(succ_l_ac_sb, step_rhs), (succ_l_ac_b, eq_ac_b)],
    );

    // EQ_MID : Eq Nat (mul (mul sa sb) sc) (mul (mul sa sc) sb) --
    // "mul_right_comm" via mul_assoc / mul_comm / mul_assoc(symm).
    let sbsc = NatOps::mul(d, sb, sc);
    let scsb = NatOps::mul(d, sc, sb);
    let sa_sbsc = NatOps::mul(d, sa, sbsc);
    let sa_scsb = NatOps::mul(d, sa, scsb);
    let massoc1 = d.lemma(np.mul_assoc, &[sa, sb, sc]); // Eq sasbsc sa_sbsc
    let comm_bc = d.lemma(np.mul_comm, &[sb, sc]); // Eq sbsc scsb
    let congr_comm = NatOps::congr(d, sbsc, scsb, comm_bc, &|d, t| NatOps::mul(d, sa, t));
    let massoc2 = d.lemma(np.mul_assoc, &[sa, sc, sb]); // Eq sascsb sa_scsb
    let massoc2_symm = NatOps::symm(d, sascsb, sa_scsb, massoc2); // Eq sa_scsb sascsb
    let (_, eq_mid) = NatOps::chain(
        d,
        sasbsc,
        &[
            (sa_sbsc, massoc1),
            (sa_scsb, congr_comm),
            (sascsb, massoc2_symm),
        ],
    );

    // Combine: succ l_ab_c = sasbsc = sascsb = succ l_ac_b.
    let eq_lhs_symm = NatOps::symm(d, sasbsc, succ_l_ab_c, eq_lhs);
    let (_, final_eq) = NatOps::chain(
        d,
        succ_l_ab_c,
        &[
            (sasbsc, eq_lhs_symm),
            (sascsb, eq_mid),
            (succ_l_ac_b, eq_rhs),
        ],
    );
    // final_eq : Eq Nat (succ l_ab_c) (succ l_ac_b)
    d.lemma(np.succ_injective, &[l_ab_c, l_ac_b, final_eq])
}

/// The common-refinement construction generalized to THREE counts: given
/// `m1, m2, m3` with no assumed relationship, produces a single `L` that is
/// [`succ_mul_succ`]'s own refinement target from ALL THREE, not just two.
///
/// Construction, writing `l(x,y) := succ_mul_succ(x,y).0`: `n_refine1 :=
/// l(m2,m3)`, `L := l(n_refine1, m1)` -- [`common_refinement`]'s own
/// two-count route, reaching `m1` directly (leg 1's `n_refine`, no rewrite
/// needed). For `m3`: `n_refine3 := l(m2,m1)`, and
/// [`three_way_swap`]`(m2,m3,m1)` gives `L = l(l(m2,m3),m1) =
/// l(l(m2,m1),m3) = l(n_refine3,m3)` directly. For `m2`:
/// [`common_refinement`]`(m2,m3)`'s own third return (`l(m2,m3) =
/// l(m3,m2)`) rewrites `n_refine1` inside `L`'s formula to `l(m3,m2)`, then
/// [`three_way_swap`]`(m3,m2,m1)` reaches `n_refine2 := l(m3,m1)` as the
/// OUTER base.
///
/// Returns `(L, n_refine1, n_refine2, eq2, n_refine3, eq3)`: `n_refine1` is
/// used DIRECTLY (`L = succ_mul_succ(n_refine1, m1).0`, by construction, no
/// rewrite); `eq2 : Eq Nat L (succ_mul_succ n_refine2 m2).0` and `eq3 : Eq
/// Nat L (succ_mul_succ n_refine3 m3).0` are the two extra bridges
/// [`common_refinement`] alone cannot give.
fn common_refinement3(
    d: &mut IntDev<'_>,
    m1: ExprId,
    m2: ExprId,
    m3: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId, ExprId) {
    // (l_m3_m2, n_refine1, symm23) = common_refinement(m2,m3):
    //   l_m3_m2 = l(m3,m2), n_refine1 = l(m2,m3), symm23 : Eq n_refine1 l_m3_m2.
    let (l_m3_m2, n_refine1, symm23) = common_refinement(d, m2, m3);
    let l_val = succ_mul_succ(d, n_refine1, m1).0; // L = l(n_refine1, m1)

    let n_refine3 = succ_mul_succ(d, m2, m1).0; // l(m2,m1)
    let eq3 = three_way_swap(d, m2, m3, m1);
    // eq3 : Eq (l(l(m2,m3),m1)) (l(l(m2,m1),m3)) = Eq L (l(n_refine3,m3))

    let congr_step = NatOps::congr(d, n_refine1, l_m3_m2, symm23, &|d, t| {
        succ_mul_succ(d, t, m1).0
    });
    // congr_step : Eq L (l(l_m3_m2,m1)) = Eq L (l(l(m3,m2),m1))
    let swap312 = three_way_swap(d, m3, m2, m1);
    // swap312 : Eq (l(l(m3,m2),m1)) (l(l(m3,m1),m2))
    let n_refine2 = succ_mul_succ(d, m3, m1).0; // l(m3,m1)
    let l_m3m2_m1 = succ_mul_succ(d, l_m3_m2, m1).0;
    let l_n_refine2_m2 = succ_mul_succ(d, n_refine2, m2).0;
    let (_, eq2) = NatOps::chain(
        d,
        l_val,
        &[(l_m3m2_m1, congr_step), (l_n_refine2_m2, swap312)],
    );

    (l_val, n_refine1, n_refine2, eq2, n_refine3, eq3)
}

#[cfg(test)]
mod common_refinement3_tests {
    use super::*;
    use crate::Declaration;

    /// **The load-bearing check.** [`common_refinement3`] at SYMBOLIC `m1,
    /// m2, m3` -- a concrete instantiation could pass by pure computation
    /// even with a wrong `Nat.mul_comm`/`Nat.mul_assoc` step, exactly the
    /// trap [`common_refinement`]'s own test module documents for the
    /// two-count case.
    #[test]
    fn common_refinement3_type_checks_symbolically() {
        crate::on_a_deep_stack(common_refinement3_type_checks_symbolically_body);
    }

    fn common_refinement3_type_checks_symbolically_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();

        let m1_fv = d.fresh_fvar();
        let m1 = d.kernel().fvar(m1_fv);
        let m2_fv = d.fresh_fvar();
        let m2 = d.kernel().fvar(m2_fv);
        let m3_fv = d.fresh_fvar();
        let m3 = d.kernel().fvar(m3_fv);

        let (l_val, n_refine1, n_refine2, eq2, n_refine3, eq3) =
            common_refinement3(&mut d, m1, m2, m3);

        // eq2 : Eq Nat l_val (succ_mul_succ n_refine2 m2).0
        let l_from2 = succ_mul_succ(&mut d, n_refine2, m2).0;
        let ty2 = d.eq(l_val, l_from2);
        let with_m3 = d.pi_fv(m3_fv, nat, ty2);
        let with_m2 = d.pi_fv(m2_fv, nat, with_m3);
        let ty2_full = d.pi_fv(m1_fv, nat, with_m2);
        let value2 = {
            let with_m3 = d.lam_fv(m3_fv, nat, eq2);
            let with_m2 = d.lam_fv(m2_fv, nat, with_m3);
            d.lam_fv(m1_fv, nat, with_m2)
        };
        let anon = d.kernel().anon();
        let name2 = d.kernel().name_str(anon, "commonRefinement3SmokeEq2");
        let result2 = d.kernel().add_declaration(Declaration::Theorem {
            name: name2,
            uparams: vec![],
            ty: ty2_full,
            value: value2,
        });
        assert!(
            result2.is_ok(),
            "common_refinement3's eq2 must type-check symbolically: {:?}",
            result2.err()
        );

        // eq3 : Eq Nat l_val (succ_mul_succ n_refine3 m3).0
        let l_from3 = succ_mul_succ(&mut d, n_refine3, m3).0;
        let ty3 = d.eq(l_val, l_from3);
        let ty3_full = {
            let with_m3 = d.pi_fv(m3_fv, nat, ty3);
            let with_m2 = d.pi_fv(m2_fv, nat, with_m3);
            d.pi_fv(m1_fv, nat, with_m2)
        };
        let value3 = {
            let with_m3 = d.lam_fv(m3_fv, nat, eq3);
            let with_m2 = d.lam_fv(m2_fv, nat, with_m3);
            d.lam_fv(m1_fv, nat, with_m2)
        };
        let name3 = d.kernel().name_str(anon, "commonRefinement3SmokeEq3");
        let result3 = d.kernel().add_declaration(Declaration::Theorem {
            name: name3,
            uparams: vec![],
            ty: ty3_full,
            value: value3,
        });
        assert!(
            result3.is_ok(),
            "common_refinement3's eq3 must type-check symbolically: {:?}",
            result3.err()
        );

        // Direct check: n_refine1 IS the value that makes L = l(n_refine1,m1)
        // hold with NO rewrite -- confirm it type-checks as a plain Eq.refl.
        let l_direct = succ_mul_succ(&mut d, n_refine1, m1).0;
        assert_eq!(
            l_val, l_direct,
            "L must literally BE succ_mul_succ(n_refine1, m1).0, no rewrite"
        );

        // Negative control: eq2 must be REFUSED at the WRONG target
        // `succ_mul_succ(n_refine3, m2).0` (mixing the wrong refine factor
        // with the wrong base).
        let wrong = succ_mul_succ(&mut d, n_refine3, m2).0;
        let wrong_ty = d.eq(l_val, wrong);
        let wrong_ty_full = {
            let with_m3 = d.pi_fv(m3_fv, nat, wrong_ty);
            let with_m2 = d.pi_fv(m2_fv, nat, with_m3);
            d.pi_fv(m1_fv, nat, with_m2)
        };
        let value_bad = {
            let with_m3 = d.lam_fv(m3_fv, nat, eq2);
            let with_m2 = d.lam_fv(m2_fv, nat, with_m3);
            d.lam_fv(m1_fv, nat, with_m2)
        };
        let name_bad = d.kernel().name_str(anon, "commonRefinement3SmokeBad");
        let result_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_bad,
            uparams: vec![],
            ty: wrong_ty_full,
            value: value_bad,
        });
        assert!(
            result_bad.is_err(),
            "eq2 must be REFUSED against the mismatched target mixing n_refine3 with m2"
        );
    }
}

#[cfg(test)]
mod sample_offset_bound_tests {
    use super::*;
    use crate::Declaration;

    /// Wraps [`sample_offset_bound`] (roadmap step 1's per-term fine-vs-coarse
    /// bound, toward `riemannSum_cauchy`) in a throwaway anonymous theorem,
    /// symbolically in `base, delta, n, j`, and lets the kernel accept or
    /// reject it -- the same idiom as `succ_shape_bridge_tests` above.
    #[test]
    fn sample_offset_bound_type_checks_symbolically() {
        crate::on_a_deep_stack(sample_offset_bound_type_checks_symbolically_body);
    }

    fn sample_offset_bound_type_checks_symbolically_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);
        let nat = d.nat_ty();

        let base_fv = d.fresh_fvar();
        let base = d.kernel().fvar(base_fv);
        let delta_fv = d.fresh_fvar();
        let delta = d.kernel().fvar(delta_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let n_succ = d.succ(n);
        let hlt_ty = d.lt(j, n_succ);
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);

        let zero_c = czero(&mut d, p);
        let delta_nonneg_ty = cle(&mut d, p, zero_c, delta);
        let delta_nonneg_fv = d.fresh_fvar();
        let delta_nonneg = d.kernel().fvar(delta_nonneg_fv);

        let proof_body = sample_offset_bound(&mut d, p, base, delta, n, j, hlt, delta_nonneg);

        // Reconstruct the same conclusion type independently -- `le (abs
        // diff) delta`, `diff := (base + mul (ofNat j) (mul delta (embed
        // (natDivSucc 1 n)))) + (neg base)`.
        let one_nat = d.num(1);
        let frac_n_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
        let frac_n = embed(&mut d, p, frac_n_rat);
        let delta_fine = cmul(&mut d, p, delta, frac_n);
        let of_nat_j = d.const_app(p.of_nat, &[j]);
        let term = cmul(&mut d, p, of_nat_j, delta_fine);
        let x_j = cadd(&mut d, p, base, term);
        let nb = cneg(&mut d, p, base);
        let diff = cadd(&mut d, p, x_j, nb);
        let abs_diff = d.const_app(p.abs, &[diff]);
        let concl = cle(&mut d, p, abs_diff, delta);

        let ty = {
            let after_nonneg = d.arrow(delta_nonneg_ty, concl);
            let after_hlt = d.arrow(hlt_ty, after_nonneg);
            let over_j = d.pi_fv(j_fv, nat, after_hlt);
            let over_n = d.pi_fv(n_fv, nat, over_j);
            let over_delta = d.pi_fv(delta_fv, carrier, over_n);
            d.pi_fv(base_fv, carrier, over_delta)
        };
        let value = {
            let with_nonneg = d.lam_fv(delta_nonneg_fv, delta_nonneg_ty, proof_body);
            let with_hlt = d.lam_fv(hlt_fv, hlt_ty, with_nonneg);
            let over_j = d.lam_fv(j_fv, nat, with_hlt);
            let over_n = d.lam_fv(n_fv, nat, over_j);
            let over_delta = d.lam_fv(delta_fv, carrier, over_n);
            d.lam_fv(base_fv, carrier, over_delta)
        };

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "sampleOffsetBoundSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "sample_offset_bound must type-check: {:?}",
            result.err()
        );
    }
}

#[cfg(test)]
mod le_add_of_abs_sub_le_tests {
    use super::*;
    use crate::Declaration;

    /// The mandatory concrete instantiation: `x := ofNat 3`, `y := ofNat 2`,
    /// `q := Rat.natDivSucc 1 0` (`= 1`) — the TIGHT boundary case `3 ≤ 2 +
    /// 1`, chosen (per this slice's own caution about argument-order
    /// defects) so that swapping `x`/`y`, or adding `q` on the wrong side,
    /// produces a DIFFERENT concrete conclusion type than the one this test
    /// reconstructs independently -- the kernel's own type-checker is what
    /// catches the mismatch, not a comment.
    ///
    /// `h` (the hypothesis `le (abs (add x (neg y))) (ofRat q)`) is left an
    /// assumed free variable rather than proved from scratch — proving it
    /// numerically would need `ofNat` subtraction reduction, `abs` of a
    /// literal, and a `Rat` literal identity, none of which this slice's
    /// declaration itself needs. What this test checks is exactly what the
    /// declaration's own TYPE promises: applying it at concrete literals
    /// yields a term whose type is the expected concrete conclusion.
    #[test]
    fn le_add_of_abs_sub_le_applies_at_three_two_and_one() {
        crate::on_a_deep_stack(le_add_of_abs_sub_le_applies_at_three_two_and_one_body);
    }

    fn le_add_of_abs_sub_le_applies_at_three_two_and_one_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let three = d.num(3);
        let two = d.num(2);
        let x = d.const_app(p.of_nat, &[three]);
        let y = d.const_app(p.of_nat, &[two]);

        let one_nat = d.num(1);
        let zero_nat = d.num(0);
        let q = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]); // 1/(0+1) = 1

        let ny = cneg(&mut d, p, y);
        let diff = cadd(&mut d, p, x, ny);
        let abs_diff = d.const_app(p.abs, &[diff]);
        let q_embed = embed(&mut d, p, q);
        let hyp_ty = cle(&mut d, p, abs_diff, q_embed);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let applied = d.const_app(p.le_add_of_abs_sub_le, &[x, y, q, h]);

        // Independently reconstruct the expected conclusion: le x (add y
        // q_embed), i.e. `3 ≤ 2 + 1`.
        let yq = cadd(&mut d, p, y, q_embed);
        let expected = cle(&mut d, p, x, yq);

        let ty = d.arrow(hyp_ty, expected);
        let value = d.lam_fv(h_fv, hyp_ty, applied);

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "leAddOfAbsSubLeThreeTwoOneSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "le_add_of_abs_sub_le must apply at (3, 2, 1) with the expected \
             conclusion type: {:?}",
            result.err()
        );
    }
}

#[cfg(test)]
mod two_sided_of_abs_sub_le_tests {
    use super::*;
    use crate::Declaration;

    /// The mandatory concrete instantiation, same triple as
    /// `le_add_of_abs_sub_le_applies_at_three_two_and_one`: `x := 3`,
    /// `y := 2`, `q := 1`, expecting `And (le 3 (2+1)) (le 2 (3+1))` --
    /// both conjuncts tight (`3 ≤ 3`, and `2 ≤ 4` slack), independently
    /// reconstructed so a swapped conjunct, or a conclusion built from the
    /// wrong endpoint, fails to match.
    #[test]
    fn two_sided_of_abs_sub_le_applies_at_three_two_and_one() {
        crate::on_a_deep_stack(two_sided_of_abs_sub_le_applies_at_three_two_and_one_body);
    }

    fn two_sided_of_abs_sub_le_applies_at_three_two_and_one_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let logic = p.rat.int.logic;

        let three = d.num(3);
        let two = d.num(2);
        let x = d.const_app(p.of_nat, &[three]);
        let y = d.const_app(p.of_nat, &[two]);

        let one_nat = d.num(1);
        let zero_nat = d.num(0);
        let q = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]); // 1/(0+1) = 1

        let ny = cneg(&mut d, p, y);
        let diff = cadd(&mut d, p, x, ny);
        let abs_diff = d.const_app(p.abs, &[diff]);
        let q_embed = embed(&mut d, p, q);
        let hyp_ty = cle(&mut d, p, abs_diff, q_embed);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let applied = d.const_app(p.two_sided_of_abs_sub_le, &[x, y, q, h]);

        // Independently reconstruct: And (le x (add y q_embed)) (le y (add x
        // q_embed)), i.e. `And (3 ≤ 2 + 1) (2 ≤ 3 + 1)`.
        let yq = cadd(&mut d, p, y, q_embed);
        let xq = cadd(&mut d, p, x, q_embed);
        let left_ty = cle(&mut d, p, x, yq);
        let right_ty = cle(&mut d, p, y, xq);
        let expected = d.const_app(logic.and, &[left_ty, right_ty]);

        let ty = d.arrow(hyp_ty, expected);
        let value = d.lam_fv(h_fv, hyp_ty, applied);

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "twoSidedOfAbsSubLeThreeTwoOneSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "two_sided_of_abs_sub_le must apply at (3, 2, 1) with the \
             expected conclusion type: {:?}",
            result.err()
        );
    }
}

#[cfg(test)]
mod fine_block_sum_close_tests {
    use super::*;
    use crate::Declaration;

    /// The mandatory concrete instantiation: `F := fun x => x` (so
    /// `u := CReal.uniformly_continuous_id a b` is a REAL witness, not a
    /// placeholder), `a := 0`, `b := 1`, `e := 0`, `m := 2`, `n := 1`,
    /// `i := 1` -- `m != n` and `i != 0`, per this slice's own caution that a
    /// transposed-argument defect is invisible at equal/zero indices.
    /// `hab`/`hi`/`hge` are left assumed (proving them numerically needs
    /// `bound`/`Nat.le` computation this declaration's own TYPE does not
    /// need), so what this test checks is exactly the declaration's own
    /// promise: applying it at these literals yields a term whose type is
    /// the expected concrete `And` conclusion, independently reconstructed
    /// from the same `delta_nonneg_of`/`sample_point`/`summand_fn` building
    /// blocks the real declaration uses.
    #[test]
    fn fine_block_sum_close_applies_at_concrete_literals() {
        crate::on_a_deep_stack(fine_block_sum_close_applies_at_concrete_literals_body);
    }

    fn fine_block_sum_close_applies_at_concrete_literals_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let carrier = creal_ty(&mut d, p);
        let identity_body = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            d.lam_fv(x_fv, carrier, x)
        };

        let zero_nat = d.num(0);
        let one_nat_lit = d.num(1);
        let a = d.const_app(p.of_nat, &[zero_nat]);
        let b = d.const_app(p.of_nat, &[one_nat_lit]);
        let e = d.num(0);
        let m = d.num(2);
        let n = d.num(1);
        let i = d.num(1);

        let u = d.const_app(p.uniformly_continuous_id, &[a, b]);

        let hab_ty = cle(&mut d, p, a, b);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);

        let hi_ty = d.le(i, m);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);

        // deep, the same way the real declaration computes it, at F :=
        // identity (so `modulus_fn` reduces to `fun n => n`, though this
        // test does not need that reduction to build the HYPOTHESIS type).
        let modulus_fn = d.const_app(p.uc_modulus, &[identity_body, a, b, u]);
        let outer = d.apply(modulus_fn, &[e]);
        let width = width_of(&mut d, p, a, b);
        let (c, magnitude, _width_le_mag) = direct_bound_le(&mut d, p, width);
        let me = NatOps::mul(&mut d, magnitude, outer);
        let deep = NatOps::add(&mut d, me, c);
        let hge_ty = d.le(deep, m);
        let hge_fv = d.fresh_fvar();
        let hge = d.kernel().fvar(hge_fv);

        let applied = d.const_app(
            p.fine_block_sum_close,
            &[identity_body, a, b, e, m, n, i, hab, u, hi, hge],
        );

        // Independently reconstruct the expected conclusion, using the same
        // building blocks `declare_fine_block_sum_close` itself uses.
        let (delta_m, _delta_m_nonneg) = delta_nonneg_of(&mut d, p, a, b, m, hab);
        let base_i = sample_point(&mut d, p, a, delta_m, i);
        let fbase = d.apply(identity_body, &[base_i]);
        let one_nat = d.num(1);
        let frac_n_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
        let frac_n = embed(&mut d, p, frac_n_rat);
        let delta_fine = cmul(&mut d, p, delta_m, frac_n);
        let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
        let eps_embed = embed(&mut d, p, eps_rat);
        let sn = d.succ(n);

        let block_summand = summand_fn(&mut d, p, identity_body, base_i, delta_fine);
        let block_sum = d.const_app(p.sum_range, &[block_summand, sn]);
        let coarse_term = cmul(&mut d, p, fbase, delta_m);
        let eps_term = cmul(&mut d, p, eps_embed, delta_m);
        let coarse_plus_eps = cadd(&mut d, p, coarse_term, eps_term);
        let block_sum_plus_eps = cadd(&mut d, p, block_sum, eps_term);
        let upper_ty = cle(&mut d, p, block_sum, coarse_plus_eps);
        let lower_ty = cle(&mut d, p, coarse_term, block_sum_plus_eps);
        let logic = p.rat.int.logic;
        let expected = d.const_app(logic.and, &[upper_ty, lower_ty]);

        let ty = {
            let after_hge = d.arrow(hge_ty, expected);
            let after_hi = d.arrow(hi_ty, after_hge);
            d.arrow(hab_ty, after_hi)
        };
        let value = {
            let with_hge = d.lam_fv(hge_fv, hge_ty, applied);
            let with_hi = d.lam_fv(hi_fv, hi_ty, with_hge);
            d.lam_fv(hab_fv, hab_ty, with_hi)
        };

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "fineBlockSumCloseConcreteLiteralsSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "fine_block_sum_close must apply at (identity, 0, 1, e=0, m=2, \
             n=1, i=1) with the expected conclusion type: {:?}",
            result.err()
        );
    }
}

#[cfg(test)]
mod mesh_reciprocal_mul_tests {
    use super::*;
    use crate::Declaration;

    /// The mandatory concrete instantiation: `n := 1, m := 2` (`n != m`, per
    /// this slice's own caution about transposed-argument defects). `m_prime
    /// = (n*m)+n+m = 2+1+2 = 5`, and `(succ n)*(succ m) = 2*3 = 6 = succ 5`,
    /// so `natDivSucc 1 5 = 1/6` should equal `natDivSucc 1 1 * natDivSucc 1
    /// 2 = (1/2)*(1/3)`. This test is the load-bearing check on the
    /// declaration's OWN central claim -- that the kernel's conversion
    /// checker actually bridges `Nat.mul (succ n) (succ m)` down to `succ
    /// m_prime` and `Int.mul (ofNat 1) (ofNat 1)` down to `ofNat 1` with no
    /// extra rewrite step -- applied at concrete literals where every
    /// intermediate `Nat`/`Int` computation fully reduces, not merely
    /// symbolically.
    #[test]
    fn mesh_reciprocal_mul_applies_at_one_two_and_reduces_to_five() {
        crate::on_a_deep_stack(mesh_reciprocal_mul_applies_at_one_two_and_reduces_to_five_body);
    }

    fn mesh_reciprocal_mul_applies_at_one_two_and_reduces_to_five_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let n = d.num(1);
        let m = d.num(2);
        let applied = d.const_app(p.mesh_reciprocal_mul, &[n, m]);

        // Independently reconstruct the expected conclusion at the literal
        // `m_prime := 5`, NOT by recomputing `((n*m)+n)+m` symbolically --
        // the whole point is to check the declaration's result against a
        // literal the test built independently.
        let one_nat = d.num(1);
        let five = d.num(5);
        let dn = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
        let dm = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
        let lhs = rmul(&mut d, dn, dm);
        let rhs = d.const_app(p.rat.nat_div_succ, &[one_nat, five]);
        let expected = req(&mut d, lhs, rhs);

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "meshReciprocalMulOneTwoFiveSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected,
            value: applied,
        });
        assert!(
            result.is_ok(),
            "mesh_reciprocal_mul at (1, 2) must have type Eq Rat \
             (natDivSucc 1 1 * natDivSucc 1 2) (natDivSucc 1 5): {:?}",
            result.err()
        );
    }
}

#[cfg(test)]
mod equiv_abs_diff_le_tests {
    use super::*;
    use crate::Declaration;

    /// The mandatory concrete instantiation: `x := y := ofNat 3` (so `hxy`
    /// is a REAL proof, `equiv_refl (ofNat 3)`, not an assumed free
    /// variable) and `e := 0`, expecting `le (abs (add x (neg x))) (embed
    /// (natDivSucc 1 0))` -- independently reconstructed so a swapped
    /// argument or a wrong target bound fails to match.
    #[test]
    fn equiv_abs_diff_le_applies_at_equal_literals() {
        crate::on_a_deep_stack(equiv_abs_diff_le_applies_at_equal_literals_body);
    }

    fn equiv_abs_diff_le_applies_at_equal_literals_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let three = d.num(3);
        let x = d.const_app(p.of_nat, &[three]);
        let hxy = d.lemma(p.equiv_refl, &[x]);
        let zero_nat = d.num(0);

        let applied = d.const_app(p.equiv_abs_diff_le, &[x, x, hxy, zero_nat]);

        let diff = {
            let nx = cneg(&mut d, p, x);
            cadd(&mut d, p, x, nx)
        };
        let abs_diff = d.const_app(p.abs, &[diff]);
        let one_nat = d.num(1);
        let q = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let embed_q = embed(&mut d, p, q);
        let expected = cle(&mut d, p, abs_diff, embed_q);

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "equivAbsDiffLeEqualLiteralsSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected,
            value: applied,
        });
        assert!(
            result.is_ok(),
            "equiv_abs_diff_le at (ofNat 3, ofNat 3, refl, 0) must have the \
             expected conclusion type: {:?}",
            result.err()
        );
    }
}

// --- the per-block fold: gluing `sumRange_reblock`'s flat sum to
// `fineBlockSum_close`'s per-block sum ---------------------------------------
//
// `CReal.sumRange_reblock` regroups an arbitrary `g : Nat -> CReal` summed
// over `(succ n)*(succ m)` terms into `succ m` consecutive blocks of `succ n`
// terms each (`reblock_block`, this file's own private helper). Read at
// `g := summand_fn F a delta_m_prime` -- exactly `riemannSum F a b m_prime`'s
// own summand at the REFINED total subdivision count `m_prime`
// (`succ m_prime = (succ n)*(succ m)` by `succ_mul_succ`, the identity
// `samplePoint_reblock`/`meshReciprocalMul` already use) -- block `i`'s own
// flat sum is `sumRange (fun j => g ((succ n)*i + j)) (succ n)`, applying `F`
// at the RAW global fine index. `CReal.fineBlockSum_close` instead bounds a
// sum built from the LOCAL per-block arithmetic (`base_i := sample_point a
// delta_m i`, `delta_fine := delta_m * natDivSucc(1, n)`), applying `F` at
// `base_i + j*delta_fine`.
//
// This section proves the two sums are `Equiv`, EXACTLY (no error term at
// all) -- the missing link `fineBlockSum_close`'s own per-block bound needs
// before it can say anything about `sumRange_reblock`'s flat global sum. Two
// obstructions, both already solved elsewhere in this file:
//
// - The two sample points (`sample_point a delta_m_prime globalIdx` and
//   `sample_point base_i delta_fine j`) are only `Equiv`, not syntactically
//   equal (`samplePoint_reblock`, roadmap step 1) -- and `CReal -> CReal`
//   functions are NOT automatically `Equiv`-respecting in this setoid
//   (ADR-0512). `CReal.equivAbsDiffLe` turns the exact `Equiv` into an
//   explicit bound at every accuracy `e`, `UniformlyContinuousOn.spec` lifts
//   that through `F`, and `CReal.equiv_zero_of_small` (`archimedean_squeeze.rs`)
//   promotes the resulting `∀ e, …` bound back to a full `Equiv (F x) (F y)`.
// - Both sample points need to be placed in `[a, b]` before `spec` applies:
//   the LOCAL point is `CReal.fineSample_in_bounds`'s own `x` exactly; the
//   RAW GLOBAL point needs its index in `Nat.succ`-shape
//   (`riemannSum_sample_in_bounds` takes a `Nat.lt _ (Nat.succ _)` bound),
//   which `Nat.mul_succ_add_lt_of_le_of_lt` (roadmap step 2,
//   `nat_prelude/order.rs`) gives directly at `(succ n)*(succ m)`, transported
//   along `succ_mul_succ`'s own identity to `succ m_prime`.
//
// Roadmap step 4 (the outer fold over all `succ m` coarse blocks) and step 5
// (assembly into `riemannSum_cauchy` via `within_of_two_sided_le`) are
// explicitly NOT attempted here.

/// `∀ i, Nat.lt i bound → Equiv (f i) (g i)` — the bounded pointwise `Equiv`
/// hypothesis a `sumRange`-congruence induction restricted to `Nat.lt`
/// needs. Reproduces the shape of `series.rs`'s private `bounded_le_pointwise`
/// with `CReal.Equiv` in place of `CReal.le` (that file is out of scope for
/// edits in this slice, so this rebuilds the shape rather than importing it).
fn bounded_equiv_pointwise(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    g: ExprId,
    bound: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let eqv = equiv(d, p, fi, gi);
    let body = d.arrow(hyp, eqv);
    d.pi_fv(i_fv, nat, body)
}

/// Proof of `bounded_equiv_pointwise(f, g, k) → Equiv (sumRange f k)
/// (sumRange g k)`, by induction on `k`. `series.rs`'s own `CReal.sumRange_congr`
/// takes an UNRESTRICTED pointwise hypothesis (`∀ i, Equiv (f i) (g i)`, no
/// bound on `i`), too strong for [`pointwise_block_equiv`]: it can only place
/// a fine sample point in `[a, b]` for `j < Nat.succ n`. This is the
/// `Nat.lt`-bounded analogue instead, mirroring `series.rs`'s own bounded
/// `CReal.sumRange_le` induction (`add_congr` in place of `add_le_add`).
/// Kept private/file-local rather than a new `CRealPrelude` name --
/// [`declare_reblock_block_eq_fine_block_sum`] is its only call site.
fn sum_range_congr_lt_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    g: ExprId,
    k: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_equiv_pointwise(d, p, f, g, x);
        let lhs = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.const_app(p.sum_range, &[g, x]);
        let concl = equiv(d, p, lhs, rhs);
        d.arrow(hyp, concl)
    };
    d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = bounded_equiv_pointwise(d, p, f, g, zero);
            let h_fv = d.fresh_fvar();
            let zero_c = czero(d, p);
            let body = d.lemma(p.equiv_refl, &[zero_c]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_equiv_pointwise(d, p, f, g, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // h_lt_j : ∀ i, Nat.lt i j → Equiv (f i) (g i), weakened from `h`.
            let h_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let np = d.prelude();
                let le_succ_j = d.lemma(np.le_succ, &[j]);
                let lifted = d.lemma(np.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let np = d.prelude();
            let lt_j_sj = d.lemma(np.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let f_prior = d.const_app(p.sum_range, &[f, j]);
            let g_prior = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let body = d.lemma(p.add_congr, &[f_prior, g_prior, fj, gj, sub1, sub2]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        k,
    )
}

/// `Equiv (add (neg x) x) zero` — the commuted form of `add_neg`. Reproduced
/// verbatim from `monotone.rs`'s private `neg_add_self` (that file is out of
/// scope for edits in this slice).
fn neg_add_self_local(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let x_nx = cadd(d, p, x, nx);
    let nx_x = cadd(d, p, nx, x);
    let comm = d.lemma(p.add_comm, &[x, nx]);
    let comm_symm = d.lemma(p.equiv_symm, &[x_nx, nx_x, comm]);
    let cancel = d.lemma(p.add_neg, &[x]);
    echain(d, p, nx_x, &[(x_nx, comm_symm), (zero_c, cancel)])
}

/// From `h : Equiv (add a (neg b)) zero`, derive `Equiv a b` — the general
/// "a difference `Equiv` to zero means the two sides are `Equiv`" bridge.
/// Reproduced verbatim from `monotone.rs`'s private `equiv_of_sub_equiv_zero`
/// (that file is out of scope for edits in this slice).
fn equiv_of_sub_equiv_zero_local(
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
        let nas = neg_add_self_local(d, p, b);
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        let cong = d.lemma(p.add_congr, &[a, a, nb_b, zero_c, refl_a, nas]);
        let a_zero = cadd(d, p, a, zero_c);
        let trim = d.lemma(p.add_zero, &[a]);
        echain(d, p, lhs, &[(a_nbb, assoc), (a_zero, cong), (a, trim)])
    };
    let b_from_lhs = {
        let refl_b = d.lemma(p.equiv_refl, &[b]);
        let cong = d.lemma(p.add_congr, &[diff, zero_c, b, b, h, refl_b]);
        let zero_b = cadd(d, p, zero_c, b);
        let comm = d.lemma(p.add_comm, &[zero_c, b]);
        let b_zero = cadd(d, p, b, zero_c);
        let trim = d.lemma(p.add_zero, &[b]);
        echain(d, p, lhs, &[(zero_b, cong), (b_zero, comm), (b, trim)])
    };
    let a_from_lhs_symm = d.lemma(p.equiv_symm, &[lhs, a, a_from_lhs]);
    d.lemma(p.equiv_trans, &[a, lhs, b, a_from_lhs_symm, b_from_lhs])
}

/// The per-fine-index proof `Equiv (g_shifted j) (block_summand j)`, at a
/// free `j` with `hj : Nat.lt j (Nat.succ n)` -- the pointwise hypothesis
/// [`sum_range_congr_lt_proof`] needs. `g_shifted j` is defeq `mul (F
/// (sample_point a delta_m_prime globalIdx)) delta_m_prime`
/// (`summand_fn F a delta_m_prime` applied at the RAW global index
/// `globalIdx := (succ n)*i + j`); `block_summand j` is defeq `mul (F
/// (sample_point base_i delta_fine j)) delta_fine` (`summand_fn F base_i
/// delta_fine` applied at `j`).
///
/// Route: [`sample_point_reblock_proof`] gives the exact (unconditional)
/// sample-point `Equiv`; `Nat.mul_succ_add_lt_of_le_of_lt` (transported
/// along [`succ_mul_succ`]'s own identity) places the global sample point in
/// `[a, b]` via [`CRealPrelude::riemann_sample_in_bounds`]
/// (accessed as `p.riemann_sample_in_bounds`), and
/// [`CRealPrelude::fine_sample_in_bounds`] places the local one directly;
/// [`CRealPrelude::equiv_abs_diff_le`] turns the sample-point `Equiv` into
/// the explicit distance bound [`CRealPrelude::uc_spec`] demands at every
/// accuracy, and [`CRealPrelude::equiv_zero_of_small`] plus
/// [`equiv_of_sub_equiv_zero_local`] promote the resulting `∀ e, …` bound
/// back to a full `Equiv (F lhs_pt) (F rhs_pt)`; [`mesh_reblock_delta_eq`]'s
/// own mesh identity folds that, via `mul_congr`, into the actual per-term
/// shape.
#[allow(clippy::too_many_arguments)]
fn pointwise_block_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    m: ExprId,
    n: ExprId,
    i: ExprId,
    j: ExprId,
    hab: ExprId,
    hi: ExprId,
    hj: ExprId,
    u: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let logic = p.rat.int.logic;

    // The sample-point identity (unconditional in `i`, `j`).
    let (lhs_pt, rhs_pt, hsp) = sample_point_reblock_proof(d, p, a, b, n, m, i, j);

    // The mesh identity, independently (`sample_point_reblock_proof` needs
    // its own internal copy; `delta_m_prime`/`delta_fine`/`delta_eq` are
    // needed again below to fold the outer `delta` factor).
    let (m_prime, succ_proof) = succ_mul_succ(d, n, m);
    let width = width_of(d, p, a, b);
    let (delta_m_prime, delta_fine, delta_eq) = mesh_reblock_delta_eq(d, p, width, n, m, m_prime);

    // Place `lhs_pt` (the raw global fine sample point) in `[a, b]`: the
    // global index needs a `Nat.succ`-shaped bound, from
    // `Nat.mul_succ_add_lt_of_le_of_lt` (roadmap step 2) transported along
    // `succ_mul_succ`'s own identity.
    let np = d.prelude();
    let sn = d.succ(n);
    let sm = d.succ(m);
    let sn_i = NatOps::mul(d, sn, i);
    let global_idx = NatOps::add(d, sn_i, j);
    let mul_sn_sm = NatOps::mul(d, sn, sm);
    let hlt_global = d.lemma(np.mul_succ_add_lt_of_le_of_lt, &[n, m, i, j, hi, hj]);
    let succ_m_prime = d.succ(m_prime);
    let motive_bound = d.eq_motive(mul_sn_sm, &|d, x| d.lt(global_idx, x));
    let hlt_succ_mprime = d.transport(
        mul_sn_sm,
        motive_bound,
        hlt_global,
        succ_m_prime,
        succ_proof,
    );

    let a_le_lhs_ty = cle(d, p, a, lhs_pt);
    let lhs_le_b_ty = cle(d, p, lhs_pt, b);
    let lhs_and = d.lemma(
        p.riemann_sample_in_bounds,
        &[a, b, m_prime, global_idx, hab, hlt_succ_mprime],
    );
    let a_le_lhs = d.const_app(logic.and_left, &[a_le_lhs_ty, lhs_le_b_ty, lhs_and]);
    let lhs_le_b = d.const_app(logic.and_right, &[a_le_lhs_ty, lhs_le_b_ty, lhs_and]);

    // Place `rhs_pt` (the local per-block fine sample point) in `[a, b]`
    // directly.
    let a_le_rhs_ty = cle(d, p, a, rhs_pt);
    let rhs_le_b_ty = cle(d, p, rhs_pt, b);
    let rhs_and = d.lemma(p.fine_sample_in_bounds, &[a, b, m, n, i, j, hab, hi, hj]);
    let a_le_rhs = d.const_app(logic.and_left, &[a_le_rhs_ty, rhs_le_b_ty, rhs_and]);
    let rhs_le_b = d.const_app(logic.and_right, &[a_le_rhs_ty, rhs_le_b_ty, rhs_and]);

    // `F` respects the exact `Equiv` between the two sample points.
    let f_lhs = d.apply(f, &[lhs_pt]);
    let f_rhs = d.apply(f, &[rhs_pt]);
    let v = {
        let nfr = cneg(d, p, f_rhs);
        cadd(d, p, f_lhs, nfr)
    };
    let hyp_small = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
        let mod_e = d.apply(modulus_fn, &[e]);
        let hclose_input = d.lemma(p.equiv_abs_diff_le, &[lhs_pt, rhs_pt, hsp, mod_e]);
        let spec_out = d.lemma(
            p.uc_spec,
            &[
                f,
                a,
                b,
                u,
                e,
                lhs_pt,
                rhs_pt,
                a_le_lhs,
                lhs_le_b,
                a_le_rhs,
                rhs_le_b,
                hclose_input,
            ],
        );
        d.lam_fv(e_fv, nat, spec_out)
    };
    let v_equiv_zero = d.lemma(p.equiv_zero_of_small, &[v, hyp_small]);
    let f_equiv = equiv_of_sub_equiv_zero_local(d, p, f_lhs, f_rhs, v_equiv_zero);

    // Fold the mesh identity `delta_m_prime ~ delta_fine` through `mul_congr`
    // to reach the actual per-term shape `summand_fn`'s own `mul (F sp)
    // delta` produces.
    d.lemma(
        p.mul_congr,
        &[f_lhs, f_rhs, delta_m_prime, delta_fine, f_equiv, delta_eq],
    )
}

/// `CReal.reblockBlock_eq_fineBlockSum : ∀ F a b m n i, le a b → Nat.le i m →
/// UniformlyContinuousOn F a b → Equiv (sumRange (fun j => summand_fn F a
/// delta_m_prime ((Nat.succ n)*i + j)) (Nat.succ n)) (sumRange (summand_fn F
/// base_i delta_fine) (Nat.succ n))`, `delta_m_prime := mul (width_of a b)
/// (embed (Rat.natDivSucc 1 m_prime))` at the REFINED total count `m_prime`
/// (`succ_mul_succ`'s witness, `Nat.succ m_prime` definitionally `(Nat.succ
/// n)*(Nat.succ m)`), `base_i := sample_point a delta_m i`, `delta_fine :=
/// mul delta_m (embed (Rat.natDivSucc 1 n))`.
///
/// The per-block fold gluing `CReal.sumRange_reblock`'s flat global sum
/// (read at `g := summand_fn F a delta_m_prime` -- exactly `riemannSum F a b
/// m_prime`'s own summand) to `CReal.fineBlockSum_close`'s per-block sum: an
/// EXACT identity (no error term at all), by bounded pointwise congruence
/// ([`sum_range_congr_lt_proof`]) against [`pointwise_block_equiv`]'s
/// per-index derivation. See this section's own header comment for the two
/// obstructions it resolves and this module's own top-level documentation
/// for the overall roadmap.
///
/// Roadmap step 4 (folding this over all `Nat.succ m` coarse blocks against
/// `fineBlockSum_close`'s own `≤`-bound) and step 5 (assembling the result
/// into `riemannSum_cauchy` via `within_of_two_sided_le`) are explicitly NOT
/// attempted here.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_reblock_block_eq_fine_block_sum(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let hi_ty = d.le(i, m);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let (m_prime, _succ_proof) = succ_mul_succ(d, n, m);
    let width = width_of(d, p, a, b);
    let (delta_m_prime, delta_fine, _delta_eq) = mesh_reblock_delta_eq(d, p, width, n, m, m_prime);
    let delta_m = delta_of(d, p, a, b, m);
    let base_i = sample_point(d, p, a, delta_m, i);
    let sn = d.succ(n);

    let g = summand_fn(d, p, f, a, delta_m_prime);
    let offset = NatOps::mul(d, sn, i);
    let f_shifted = reblock_shifted_fn(d, offset, g);
    let block_summand = summand_fn(d, p, f, base_i, delta_fine);

    let hyp_proof = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hj_ty = d.lt(j, sn);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);

        let body = pointwise_block_equiv(d, p, f, a, b, m, n, i, j, hab, hi, hj, u);
        let with_hj = d.lam_fv(hj_fv, hj_ty, body);
        d.lam_fv(j_fv, nat, with_hj)
    };

    let congr_proof = sum_range_congr_lt_proof(d, p, f_shifted, block_summand, sn);
    let proof_body = d.apply(congr_proof, &[hyp_proof]);

    let concl = {
        let lhs = d.const_app(p.sum_range, &[f_shifted, sn]);
        let rhs = d.const_app(p.sum_range, &[block_summand, sn]);
        equiv(d, p, lhs, rhs)
    };

    let ty = {
        let after_u = d.arrow(u_ty, concl);
        let after_hi = d.arrow(hi_ty, after_u);
        let after_hab = d.arrow(hab_ty, after_hi);
        let over_i = d.pi_fv(i_fv, nat, after_hab);
        let over_n = d.pi_fv(n_fv, nat, over_i);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_u = d.lam_fv(u_fv, u_ty, proof_body);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_u);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hi);
        let over_i = d.lam_fv(i_fv, nat, with_hab);
        let over_n = d.lam_fv(n_fv, nat, over_i);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.reblock_block_eq_fine_block_sum,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod reblock_block_eq_fine_block_sum_tests {
    use super::*;
    use crate::Declaration;

    /// **Mandatory concrete instantiation, with a negative control.**
    /// `F := identity`, `a := zero`, `b := one`, `m := 0` (single coarse
    /// block), `n := 1` (each coarse block split into TWO fine sub-pieces,
    /// so `delta_fine := delta_m * natDivSucc(1, 1) = delta_m / 2` is
    /// genuinely half of `delta_m`, not merely `delta_m * natDivSucc(1, 0) =
    /// delta_m * 1` — `n := 0` was tried first and REJECTED as a test
    /// instance: at `n := 0` the fine and coarse meshes coincide, so a
    /// negative control built by swapping them is vacuous, exactly the
    /// degenerate-instantiation trap this session's own briefing warns
    /// about), `i := 0`. Checks that the declared theorem's proof, applied
    /// at these literals, type-checks against an INDEPENDENTLY reconstructed
    /// expected conclusion (built directly from
    /// `summand_fn`/`reblock_shifted_fn`/`sample_point`/
    /// `mesh_reblock_delta_eq`/`succ_mul_succ`, not by calling back into
    /// [`declare_reblock_block_eq_fine_block_sum`]'s own body) -- AND that
    /// the SAME proof term is REFUSED at a plausible transposed-mesh
    /// conclusion (`base_i` sampled with the COARSE mesh `delta_m` instead of
    /// the fine mesh `delta_fine`, the natural "forgot which mesh this
    /// block's own summand uses" bug). A test confirming only the expected
    /// value cannot distinguish "correct" from "compares everything equal".
    #[test]
    fn reblock_block_eq_fine_block_sum_applies_at_concrete_half_split_block() {
        crate::on_a_deep_stack(reblock_block_eq_fine_block_sum_half_split_body);
    }

    fn reblock_block_eq_fine_block_sum_half_split_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);

        let identity = {
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            d.lam_fv(r_fv, carrier, r)
        };
        let zero_c = czero(&mut d, p);
        let one_c = d.kernel().const_(p.one, vec![]);
        let zero_n = d.zero();
        let one_n = d.num(1);

        let hab = {
            let zero_lt_one = d.lemma(p.zero_lt_one, &[]);
            d.lemma(p.le_of_lt, &[zero_c, one_c, zero_lt_one])
        };
        let hi = {
            let np = d.prelude();
            d.lemma(np.le_refl, &[zero_n])
        };
        let u = d.lemma(p.uniformly_continuous_id, &[zero_c, one_c]);

        let applied = d.const_app(
            p.reblock_block_eq_fine_block_sum,
            &[identity, zero_c, one_c, zero_n, one_n, zero_n, hab, hi, u],
        );

        // Independently reconstruct the expected conclusion.
        let (m_prime0, _sp0) = succ_mul_succ(&mut d, one_n, zero_n);
        let width0 = width_of(&mut d, p, zero_c, one_c);
        let (delta_m_prime0, delta_fine0, _de0) =
            mesh_reblock_delta_eq(&mut d, p, width0, one_n, zero_n, m_prime0);
        let delta_m0 = delta_of(&mut d, p, zero_c, one_c, zero_n);
        let base_i0 = sample_point(&mut d, p, zero_c, delta_m0, zero_n);
        let sn0 = d.succ(one_n);
        let g0 = summand_fn(&mut d, p, identity, zero_c, delta_m_prime0);
        let offset0 = NatOps::mul(&mut d, sn0, zero_n);
        let f_shifted0 = reblock_shifted_fn(&mut d, offset0, g0);

        let correct_block_summand0 = summand_fn(&mut d, p, identity, base_i0, delta_fine0);
        let sum_shifted0 = d.const_app(p.sum_range, &[f_shifted0, sn0]);
        let sum_correct0 = d.const_app(p.sum_range, &[correct_block_summand0, sn0]);
        let expected = equiv(&mut d, p, sum_shifted0, sum_correct0);

        let anon = d.kernel().anon();
        let name_ok = d
            .kernel()
            .name_str(anon, "__reblockBlockEqFineBlockSumHalfSplitOk");
        let result_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: name_ok,
            uparams: vec![],
            ty: expected,
            value: applied,
        });
        assert!(
            result_ok.is_ok(),
            "reblock_block_eq_fine_block_sum at the half-split block (F := \
             id, a := zero, b := one, m := 0, n := 1, i := 0) must have the \
             expected conclusion type: {:?}",
            result_ok.err()
        );

        // Negative control: the WRONG block summand, sampled with the
        // COARSE mesh `delta_m0` instead of the fine mesh `delta_fine0` --
        // genuinely different meshes at `n := 1` (`delta_fine0` is HALF of
        // `delta_m0`), so this is not the vacuous `n := 0` collapse.
        let wrong_block_summand0 = summand_fn(&mut d, p, identity, base_i0, delta_m0);
        let sum_wrong0 = d.const_app(p.sum_range, &[wrong_block_summand0, sn0]);
        let wrong_expected = equiv(&mut d, p, sum_shifted0, sum_wrong0);
        let name_bad = d
            .kernel()
            .name_str(anon, "__reblockBlockEqFineBlockSumHalfSplitBad");
        let result_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_bad,
            uparams: vec![],
            ty: wrong_expected,
            value: applied,
        });
        assert!(
            result_bad.is_err(),
            "the SAME proof must be REFUSED against a conclusion built from \
             the coarse mesh instead of the fine one"
        );
    }
}

#[cfg(test)]
mod pointwise_block_equiv_tests {
    use super::*;
    use crate::Declaration;

    /// **Symbolic construction.** Independent evidence, beyond the
    /// whole-prelude build, that [`pointwise_block_equiv`] produces a
    /// well-typed proof term at genuinely free variables (`F, a, b, m, n, i,
    /// j` and every hypothesis), not just at the ground literals the
    /// concrete test above uses -- the same idiom as
    /// `sample_point_reblock_type_checks_symbolically`, guarding against the
    /// class of defect where a proof type-checks at every concrete instance
    /// tried but relies on a defeq shortcut (e.g. a numeral fully reducing)
    /// that a free variable does not get.
    #[test]
    fn pointwise_block_equiv_type_checks_symbolically() {
        crate::on_a_deep_stack(pointwise_block_equiv_type_checks_symbolically_body);
    }

    fn pointwise_block_equiv_type_checks_symbolically_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);
        let nat = d.nat_ty();
        let f_ty = fn_ty(&mut d, p);

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let hab_ty = cle(&mut d, p, a, b);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);

        let hi_ty = d.le(i, m);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);

        let sn = d.succ(n);
        let hj_ty = d.lt(j, sn);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);

        let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);

        let body = pointwise_block_equiv(&mut d, p, f, a, b, m, n, i, j, hab, hi, hj, u);

        // Independently reconstruct the expected conclusion.
        let (lhs_pt, rhs_pt, _hsp) = sample_point_reblock_proof(&mut d, p, a, b, n, m, i, j);
        let (m_prime, _sp) = succ_mul_succ(&mut d, n, m);
        let width = width_of(&mut d, p, a, b);
        let (delta_m_prime, delta_fine, _de) =
            mesh_reblock_delta_eq(&mut d, p, width, n, m, m_prime);
        let f_lhs = d.apply(f, &[lhs_pt]);
        let f_rhs = d.apply(f, &[rhs_pt]);
        let lhs_term = cmul(&mut d, p, f_lhs, delta_m_prime);
        let rhs_term = cmul(&mut d, p, f_rhs, delta_fine);
        let concl = equiv(&mut d, p, lhs_term, rhs_term);

        let ty = {
            let after_u = d.arrow(u_ty, concl);
            let after_hj = d.arrow(hj_ty, after_u);
            let after_hi = d.arrow(hi_ty, after_hj);
            let after_hab = d.arrow(hab_ty, after_hi);
            let over_j = d.pi_fv(j_fv, nat, after_hab);
            let over_i = d.pi_fv(i_fv, nat, over_j);
            let over_n = d.pi_fv(n_fv, nat, over_i);
            let over_m = d.pi_fv(m_fv, nat, over_n);
            let over_b = d.pi_fv(b_fv, carrier, over_m);
            let over_a = d.pi_fv(a_fv, carrier, over_b);
            d.pi_fv(f_fv, f_ty, over_a)
        };
        let value = {
            let with_u = d.lam_fv(u_fv, u_ty, body);
            let with_hj = d.lam_fv(hj_fv, hj_ty, with_u);
            let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
            let with_hab = d.lam_fv(hab_fv, hab_ty, with_hi);
            let over_j = d.lam_fv(j_fv, nat, with_hab);
            let over_i = d.lam_fv(i_fv, nat, over_j);
            let over_n = d.lam_fv(n_fv, nat, over_i);
            let over_m = d.lam_fv(m_fv, nat, over_n);
            let over_b = d.lam_fv(b_fv, carrier, over_m);
            let over_a = d.lam_fv(a_fv, carrier, over_b);
            d.lam_fv(f_fv, f_ty, over_a)
        };

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "__pointwise_block_equiv_symbolic_smoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "pointwise_block_equiv must type-check at free variables: {:?}",
            result.err()
        );
    }
}

// --- roadmap step 4: the outer fold over all `Nat.succ m` coarse blocks ---
//
// `CReal.reblockBlock_eq_fineBlockSum` (roadmap step 3) glues, EXACTLY, a
// single coarse block `i`'s reblocked fine sum to `CReal.fineBlockSum_close`'s
// own per-block sum. This section folds that identity, together with
// `fineBlockSum_close`'s own `±eps` sandwich, over ALL `Nat.succ m` coarse
// blocks at once:
//
// - `CReal.sumRange_reblock`, transported along `succ_mul_succ`'s witness
//   (`Nat.succ m_prime` definitionally `(Nat.succ n)·(Nat.succ m)`),
//   identifies the FULL reblocked sum with the REFINED `riemannSum F a b
//   m_prime`'s own sum (`riemannSum`'s definition is exactly `sumRange
//   (summand_fn F a delta) (Nat.succ _)`, see [`declare_riemann_sum`], so
//   this and the coarse identification below are both by DEFEQ, no lemma
//   needed at the top level).
// - `reblockBlock_eq_fineBlockSum`'s exact per-block `Equiv`, folded over all
//   `Nat.succ m` blocks by [`sum_range_congr_lt_proof`] (step 3's own bounded
//   congruence induction, reused here rather than duplicated), identifies
//   the reblocked sum with `fineBlockSum_close`'s own sum of per-block sums.
// - `fineBlockSum_close`'s own `±eps` sandwich, folded over all `Nat.succ m`
//   blocks with [`CRealPrelude::sum_range_le`] + [`CRealPrelude::sum_range_add`]
//   + [`CRealPrelude::sum_range_const`], accumulates to `mul (ofNat (Nat.succ
//   m)) epsTerm` -- the SAME `epsTerm` `fineBlockSum_close` already uses (it
//   does not depend on the block index `i`, so no re-derivation is needed to
//   sum it, only `CReal.sumRange_const` at the constant function).
//
// No error term accumulates from the first identification (it is an exact
// `Equiv`, not an estimate); the only error entering here is
// `fineBlockSum_close`'s own per-block `±eps`.
//
// Roadmap step 5 (assembling this into `riemannSum_cauchy` via
// `CReal.within_of_two_sided_le`, choosing `e` large enough as a function of
// the target accuracy) is explicitly NOT attempted here.

/// `fun i => sumRange (summand_fn F (sample_point a delta_m i) delta_fine)
/// sn` -- the per-block fine sub-sum `CReal.fineBlockSum_close`'s own
/// `blockSum` produces, as a function of the coarse block index `i`.
fn block_sum_fn(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    delta_m: ExprId,
    delta_fine: ExprId,
    sn: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let base_i = sample_point(d, p, a, delta_m, i);
    let block_summand = summand_fn(d, p, f, base_i, delta_fine);
    let block_sum = d.const_app(p.sum_range, &[block_summand, sn]);
    d.lam_fv(i_fv, nat, block_sum)
}

/// `(blockSum, coarseTerm, epsTerm)` at a fixed block index `i` -- rebuilt
/// the same way [`declare_fine_block_sum_close`] builds them internally, so
/// extracting either half of its `And` conclusion at `i` type-checks against
/// exactly these terms.
fn block_triple_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    delta_m: ExprId,
    delta_fine: ExprId,
    eps_embed: ExprId,
    sn: ExprId,
    i: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let base_i = sample_point(d, p, a, delta_m, i);
    let fbase = d.apply(f, &[base_i]);
    let block_summand = summand_fn(d, p, f, base_i, delta_fine);
    let block_sum = d.const_app(p.sum_range, &[block_summand, sn]);
    let coarse_term = cmul(d, p, fbase, delta_m);
    let eps_term = cmul(d, p, eps_embed, delta_m);
    (block_sum, coarse_term, eps_term)
}

/// `fun i => add (f i) (g i)` -- pointwise sum of two `Nat -> CReal`
/// functions. Reproduces the shape `series.rs`'s private `declare_sum_range_add`
/// builds its own `combined_fn` in (that file is out of scope for edits in
/// this slice), so `CReal.sumRange_add` applies against it directly once
/// substituted at concrete `f`/`g`.
fn pointwise_add_fn(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let body = cadd(d, p, fi, gi);
    d.lam_fv(i_fv, nat, body)
}

/// `CReal.riemannSum_reblock_close : ∀ F a b e m n, le a b →
/// UniformlyContinuousOn F a b → Nat.le deep m → And (le (riemannSum F a b
/// m_prime) (add (riemannSum F a b m) totalEps)) (le (riemannSum F a b m)
/// (add (riemannSum F a b m_prime) totalEps))`, `deep`
/// [`declare_fine_block_sum_close`]'s own Archimedean threshold, `m_prime`
/// [`succ_mul_succ`]'s witness, `epsTerm := mul (embed (Rat.natDivSucc 1 e))
/// delta_m` (`fineBlockSum_close`'s own per-block error term, independent of
/// the block index) and `totalEps := mul (ofNat (Nat.succ m)) epsTerm`.
///
/// Roadmap step 4: the outer fold over all `Nat.succ m` coarse blocks. See
/// this section's own header comment for the derivation and this module's
/// top-level documentation for the overall roadmap. Roadmap step 5
/// (assembling this into `riemannSum_cauchy` via
/// [`CRealPrelude::within_of_two_sided_le`]) is explicitly NOT attempted
/// here.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_reblock_close(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    // `deep`, EXACTLY as `declare_fine_block_sum_close` computes it (same
    // free variables `f, a, b, e, u` in scope, same helper calls).
    let width = width_of(d, p, a, b);
    let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let outer = d.apply(modulus_fn, &[e]);
    let (c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);
    let me = NatOps::mul(d, magnitude, outer);
    let deep = NatOps::add(d, me, c);
    let hge_ty = d.le(deep, m);
    let hge_fv = d.fresh_fvar();
    let hge = d.kernel().fvar(hge_fv);

    // `m_prime`, the refined/fine mesh identity, the coarse mesh, block
    // counts.
    let (m_prime, succ_proof) = succ_mul_succ(d, n, m);
    let (delta_m_prime, delta_fine, _delta_eq) = mesh_reblock_delta_eq(d, p, width, n, m, m_prime);
    let delta_m = delta_of(d, p, a, b, m);
    let sn = d.succ(n);
    let sm = d.succ(m);

    let g = summand_fn(d, p, f, a, delta_m_prime);
    let reblock_g = reblock_block(d, p, g, sn);
    let coarse_term_fn = summand_fn(d, p, f, a, delta_m);
    let block_sum_fn_expr = block_sum_fn(d, p, f, a, delta_m, delta_fine, sn);

    let one_nat = d.num(1);
    let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let eps_embed = embed(d, p, eps_rat);
    let eps_term = cmul(d, p, eps_embed, delta_m);

    // --- glue the FULL reblocked sum to the REFINED `riemannSum`'s own sum:
    // `Equiv (sumRange g (succ m_prime)) (sumRange reblock_g sm)`.
    let reblock_proof = sum_range_reblock_proof(d, p, g, sn, sm);
    let mul_sn_sm = NatOps::mul(d, sn, sm);
    let succ_m_prime = d.succ(m_prime);
    let reblock_g_sum = d.const_app(p.sum_range, &[reblock_g, sm]);
    let motive1 = d.eq_motive(mul_sn_sm, &|d, x| {
        let lhs = d.const_app(p.sum_range, &[g, x]);
        equiv(d, p, lhs, reblock_g_sum)
    });
    let step1 = d.transport(mul_sn_sm, motive1, reblock_proof, succ_m_prime, succ_proof);
    // step1 : Equiv (sumRange g (succ m_prime)) reblock_g_sum

    // --- glue the reblocked sum to `fineBlockSum_close`'s own sum of
    // per-block sums, EXACTLY, via `reblockBlock_eq_fineBlockSum` folded
    // over all `sm` blocks with `sum_range_congr_lt_proof`.
    let np = d.prelude();
    let step2_hyp = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_lt_ty = d.lt(i, sm);
        let hi_lt_fv = d.fresh_fvar();
        let hi_lt = d.kernel().fvar(hi_lt_fv);
        let hi_le = d.lemma(np.le_of_succ_le_succ, &[i, m, hi_lt]);
        let step3_applied = d.const_app(
            p.reblock_block_eq_fine_block_sum,
            &[f, a, b, m, n, i, hab, hi_le, u],
        );
        let inner = d.lam_fv(hi_lt_fv, hi_lt_ty, step3_applied);
        d.lam_fv(i_fv, nat, inner)
    };
    let step2 = {
        let proof_fn = sum_range_congr_lt_proof(d, p, reblock_g, block_sum_fn_expr, sm);
        d.apply(proof_fn, &[step2_hyp])
    };
    // step2 : Equiv reblock_g_sum (sumRange block_sum_fn_expr sm)

    let full_sum_g = d.const_app(p.sum_range, &[g, succ_m_prime]);
    let block_sum_total = d.const_app(p.sum_range, &[block_sum_fn_expr, sm]);
    let full_equiv = d.lemma(
        p.equiv_trans,
        &[full_sum_g, reblock_g_sum, block_sum_total, step1, step2],
    );
    // full_equiv : Equiv full_sum_g block_sum_total

    // --- fold `fineBlockSum_close`'s per-block `±eps` sandwich over all `sm`
    // blocks.
    let const_eps_fn = const_nat_fn(d, eps_term);
    let coarse_term_and_eps_fn = pointwise_add_fn(d, p, coarse_term_fn, const_eps_fn);
    let block_sum_and_eps_fn = pointwise_add_fn(d, p, block_sum_fn_expr, const_eps_fn);

    let upper_pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_lt_ty = d.lt(i, sm);
        let hi_lt_fv = d.fresh_fvar();
        let hi_lt = d.kernel().fvar(hi_lt_fv);
        let hi_le = d.lemma(np.le_of_succ_le_succ, &[i, m, hi_lt]);
        let and_i = d.const_app(
            p.fine_block_sum_close,
            &[f, a, b, e, m, n, i, hab, u, hi_le, hge],
        );
        let (block_sum_i, coarse_term_i, eps_term_i) =
            block_triple_at(d, p, f, a, delta_m, delta_fine, eps_embed, sn, i);
        let coarse_plus_eps_i = cadd(d, p, coarse_term_i, eps_term_i);
        let block_sum_plus_eps_i = cadd(d, p, block_sum_i, eps_term_i);
        let upper_ty_i = cle(d, p, block_sum_i, coarse_plus_eps_i);
        let lower_ty_i = cle(d, p, coarse_term_i, block_sum_plus_eps_i);
        let upper_i = d.const_app(logic.and_left, &[upper_ty_i, lower_ty_i, and_i]);
        let inner = d.lam_fv(hi_lt_fv, hi_lt_ty, upper_i);
        d.lam_fv(i_fv, nat, inner)
    };
    let lower_pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_lt_ty = d.lt(i, sm);
        let hi_lt_fv = d.fresh_fvar();
        let hi_lt = d.kernel().fvar(hi_lt_fv);
        let hi_le = d.lemma(np.le_of_succ_le_succ, &[i, m, hi_lt]);
        let and_i = d.const_app(
            p.fine_block_sum_close,
            &[f, a, b, e, m, n, i, hab, u, hi_le, hge],
        );
        let (block_sum_i, coarse_term_i, eps_term_i) =
            block_triple_at(d, p, f, a, delta_m, delta_fine, eps_embed, sn, i);
        let coarse_plus_eps_i = cadd(d, p, coarse_term_i, eps_term_i);
        let block_sum_plus_eps_i = cadd(d, p, block_sum_i, eps_term_i);
        let upper_ty_i = cle(d, p, block_sum_i, coarse_plus_eps_i);
        let lower_ty_i = cle(d, p, coarse_term_i, block_sum_plus_eps_i);
        let lower_i = d.const_app(logic.and_right, &[upper_ty_i, lower_ty_i, and_i]);
        let inner = d.lam_fv(hi_lt_fv, hi_lt_ty, lower_i);
        d.lam_fv(i_fv, nat, inner)
    };

    let upper_sum_le = d.lemma(
        p.sum_range_le,
        &[
            block_sum_fn_expr,
            coarse_term_and_eps_fn,
            sm,
            upper_pointwise,
        ],
    );
    // upper_sum_le : le block_sum_total (sumRange coarse_term_and_eps_fn sm)
    let lower_sum_le = d.lemma(
        p.sum_range_le,
        &[coarse_term_fn, block_sum_and_eps_fn, sm, lower_pointwise],
    );
    // lower_sum_le : le (sumRange coarse_term_fn sm) (sumRange block_sum_and_eps_fn sm)

    let coarse_sum_total = d.const_app(p.sum_range, &[coarse_term_fn, sm]);
    let const_eps_sum = d.const_app(p.sum_range, &[const_eps_fn, sm]);
    let const_sum_eps = d.lemma(p.sum_range_const, &[eps_term, m]);
    // const_sum_eps : Equiv const_eps_sum (mul (ofNat sm) eps_term)
    let sm_real = d.const_app(p.of_nat, &[sm]);
    let total_eps = cmul(d, p, sm_real, eps_term);

    // --- upper: le block_sum_total (add coarse_sum_total total_eps) -------
    let upper_final = {
        let sum_add = d.lemma(p.sum_range_add, &[coarse_term_fn, const_eps_fn, sm]);
        // sum_add : Equiv (sumRange coarse_term_and_eps_fn sm) (add
        //   coarse_sum_total const_eps_sum)
        let coarse_plus_eps_sum = cadd(d, p, coarse_sum_total, const_eps_sum);
        let coarse_plus_total_eps = cadd(d, p, coarse_sum_total, total_eps);
        let refl_coarse = d.lemma(p.equiv_refl, &[coarse_sum_total]);
        let rhs_step = d.lemma(
            p.add_congr,
            &[
                coarse_sum_total,
                coarse_sum_total,
                const_eps_sum,
                total_eps,
                refl_coarse,
                const_sum_eps,
            ],
        );
        let rhs_sum = d.const_app(p.sum_range, &[coarse_term_and_eps_fn, sm]);
        let rhs_chain = echain(
            d,
            p,
            rhs_sum,
            &[
                (coarse_plus_eps_sum, sum_add),
                (coarse_plus_total_eps, rhs_step),
            ],
        );
        let refl_block_sum_total = d.lemma(p.equiv_refl, &[block_sum_total]);
        d.lemma(
            p.le_congr,
            &[
                block_sum_total,
                block_sum_total,
                rhs_sum,
                coarse_plus_total_eps,
                refl_block_sum_total,
                rhs_chain,
                upper_sum_le,
            ],
        )
    };
    // upper_final : le block_sum_total (add coarse_sum_total total_eps)

    // --- lower: le coarse_sum_total (add block_sum_total total_eps) -------
    let lower_final = {
        let sum_add = d.lemma(p.sum_range_add, &[block_sum_fn_expr, const_eps_fn, sm]);
        // sum_add : Equiv (sumRange block_sum_and_eps_fn sm) (add
        //   block_sum_total const_eps_sum)
        let block_sum_plus_eps_sum = cadd(d, p, block_sum_total, const_eps_sum);
        let block_sum_plus_total_eps = cadd(d, p, block_sum_total, total_eps);
        let refl_block_sum = d.lemma(p.equiv_refl, &[block_sum_total]);
        let rhs_step = d.lemma(
            p.add_congr,
            &[
                block_sum_total,
                block_sum_total,
                const_eps_sum,
                total_eps,
                refl_block_sum,
                const_sum_eps,
            ],
        );
        let rhs_sum = d.const_app(p.sum_range, &[block_sum_and_eps_fn, sm]);
        let rhs_chain = echain(
            d,
            p,
            rhs_sum,
            &[
                (block_sum_plus_eps_sum, sum_add),
                (block_sum_plus_total_eps, rhs_step),
            ],
        );
        let refl_coarse_sum_total = d.lemma(p.equiv_refl, &[coarse_sum_total]);
        d.lemma(
            p.le_congr,
            &[
                coarse_sum_total,
                coarse_sum_total,
                rhs_sum,
                block_sum_plus_total_eps,
                refl_coarse_sum_total,
                rhs_chain,
                lower_sum_le,
            ],
        )
    };
    // lower_final : le coarse_sum_total (add block_sum_total total_eps)

    // --- swap `block_sum_total` for `full_sum_g` (Equiv, from `full_equiv`)
    // -- both are DEFEQ to `riemannSum F a b m_prime`/`riemannSum F a b m`
    // respectively, so the final `ty` below can state the conclusion
    // directly in terms of `riemannSum`.
    let full_equiv_symm = d.lemma(p.equiv_symm, &[full_sum_g, block_sum_total, full_equiv]);
    // full_equiv_symm : Equiv block_sum_total full_sum_g

    let coarse_plus_total_eps = cadd(d, p, coarse_sum_total, total_eps);
    let upper_result = {
        let refl_rhs = d.lemma(p.equiv_refl, &[coarse_plus_total_eps]);
        d.lemma(
            p.le_congr,
            &[
                block_sum_total,
                full_sum_g,
                coarse_plus_total_eps,
                coarse_plus_total_eps,
                full_equiv_symm,
                refl_rhs,
                upper_final,
            ],
        )
    };
    // upper_result : le full_sum_g coarse_plus_total_eps

    let full_sum_g_plus_total_eps = cadd(d, p, full_sum_g, total_eps);
    let lower_result = {
        let block_sum_plus_total_eps = cadd(d, p, block_sum_total, total_eps);
        let refl_total_eps = d.lemma(p.equiv_refl, &[total_eps]);
        let rhs_step = d.lemma(
            p.add_congr,
            &[
                block_sum_total,
                full_sum_g,
                total_eps,
                total_eps,
                full_equiv_symm,
                refl_total_eps,
            ],
        );
        let refl_coarse_lhs = d.lemma(p.equiv_refl, &[coarse_sum_total]);
        d.lemma(
            p.le_congr,
            &[
                coarse_sum_total,
                coarse_sum_total,
                block_sum_plus_total_eps,
                full_sum_g_plus_total_eps,
                refl_coarse_lhs,
                rhs_step,
                lower_final,
            ],
        )
    };
    // lower_result : le coarse_sum_total full_sum_g_plus_total_eps

    let rsum_m_prime = rsum(d, p, f, a, b, m_prime);
    let rsum_m = rsum(d, p, f, a, b, m);
    let rsum_m_plus_total_eps = cadd(d, p, rsum_m, total_eps);
    let rsum_m_prime_plus_total_eps = cadd(d, p, rsum_m_prime, total_eps);
    let upper_ty = cle(d, p, rsum_m_prime, rsum_m_plus_total_eps);
    let lower_ty = cle(d, p, rsum_m, rsum_m_prime_plus_total_eps);
    let conclusion_proof = and_intro(d, p, upper_ty, lower_ty, upper_result, lower_result);

    let ty = {
        let and_ty = d.const_app(logic.and, &[upper_ty, lower_ty]);
        let after_hge = d.arrow(hge_ty, and_ty);
        let after_u = d.pi_fv(u_fv, u_ty, after_hge);
        let after_hab = d.arrow(hab_ty, after_u);
        let over_n = d.pi_fv(n_fv, nat, after_hab);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_e = d.pi_fv(e_fv, nat, over_m);
        let over_b = d.pi_fv(b_fv, carrier, over_e);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_hge = d.lam_fv(hge_fv, hge_ty, conclusion_proof);
        let with_u = d.lam_fv(u_fv, u_ty, with_hge);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_n = d.lam_fv(n_fv, nat, with_hab);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_e = d.lam_fv(e_fv, nat, over_m);
        let over_b = d.lam_fv(b_fv, carrier, over_e);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_reblock_close,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod riemann_sum_reblock_close_tests {
    use super::*;
    use crate::Declaration;

    /// **Mandatory concrete instantiation, with a negative control.**
    /// `F := identity`, `a := ofNat 0`, `b := ofNat 1`, `e := 0`, `m := 2`,
    /// `n := 1` (`m != n`, per this slice's own caution about
    /// transposed-argument defects). `hab` and `hge` are left ASSUMED (free
    /// hypotheses) -- proving them numerically needs `CReal.bound`
    /// computation this declaration's own TYPE does not need, the same
    /// choice `fine_block_sum_close_tests` makes -- so what this test checks
    /// is exactly the declaration's own promise: applying it at these
    /// literals yields a term whose type is the expected concrete `And`
    /// conclusion, independently reconstructed from the same
    /// `rsum`/`succ_mul_succ`/`delta_of` building blocks the real
    /// declaration uses. `u := CReal.uniformly_continuous_id a b` is a REAL
    /// witness, not a placeholder.
    ///
    /// The negative control swaps `totalEps := mul (ofNat (succ m)) epsTerm`
    /// for the UNDOUBLED `epsTerm` -- the natural "forgot to multiply by the
    /// block count" bug -- and confirms the SAME proof is REFUSED against
    /// that conclusion. At `m := 2` (`succ m = 3`) `totalEps` and `epsTerm`
    /// are genuinely different `CReal` literals (a `3x` vs `1x` scaling), so
    /// this is not a vacuous check.
    #[test]
    fn riemann_sum_reblock_close_applies_at_concrete_literals() {
        crate::on_a_deep_stack(riemann_sum_reblock_close_concrete_body);
    }

    /// Fully normalizing this instantiation drives the kernel deep through
    /// nested `CReal`/`Rat`/`Int` arithmetic over a unary `Nat`, past the
    /// default 2 MiB stack. Measured 2026-08-26: SIGABRT on the default
    /// stack, `ok` under `RUST_MIN_STACK=256MiB` — a resource limit, not a
    /// proof bug.
    ///
    /// This wrapper is not optional and its absence is INVISIBLE to the lane
    /// that omits it: the author had `RUST_MIN_STACK` exported from an
    /// earlier hand-bisect, so the suite passed 93/93 in that shell and
    /// SIGABRTed in a clean one. A test whose result depends on an ambient
    /// environment variable is not a gate. Carry the stack explicitly.
    fn riemann_sum_reblock_close_concrete_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);

        let identity = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            d.lam_fv(x_fv, carrier, x)
        };

        let zero_nat = d.num(0);
        let one_nat_lit = d.num(1);
        let a = d.const_app(p.of_nat, &[zero_nat]);
        let b = d.const_app(p.of_nat, &[one_nat_lit]);
        let e = d.num(0);
        let m = d.num(2);
        let n = d.num(1);

        let u = d.const_app(p.uniformly_continuous_id, &[a, b]);

        let hab_ty = cle(&mut d, p, a, b);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);

        // `deep`, the same way the real declaration computes it.
        let modulus_fn = d.const_app(p.uc_modulus, &[identity, a, b, u]);
        let outer = d.apply(modulus_fn, &[e]);
        let width = width_of(&mut d, p, a, b);
        let (c, magnitude, _width_le_mag) = direct_bound_le(&mut d, p, width);
        let me = NatOps::mul(&mut d, magnitude, outer);
        let deep = NatOps::add(&mut d, me, c);
        let hge_ty = d.le(deep, m);
        let hge_fv = d.fresh_fvar();
        let hge = d.kernel().fvar(hge_fv);

        let applied = d.const_app(
            p.riemann_sum_reblock_close,
            &[identity, a, b, e, m, n, hab, u, hge],
        );

        // Independently reconstruct the expected conclusion.
        let (m_prime, _succ_proof) = succ_mul_succ(&mut d, n, m);
        let rsum_m_prime = rsum(&mut d, p, identity, a, b, m_prime);
        let rsum_m = rsum(&mut d, p, identity, a, b, m);

        let delta_m = delta_of(&mut d, p, a, b, m);
        let one_nat = d.num(1);
        let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
        let eps_embed = embed(&mut d, p, eps_rat);
        let eps_term = cmul(&mut d, p, eps_embed, delta_m);
        let sm = d.succ(m);
        let sm_real = d.const_app(p.of_nat, &[sm]);
        let total_eps = cmul(&mut d, p, sm_real, eps_term);

        let rsum_m_plus_total_eps = cadd(&mut d, p, rsum_m, total_eps);
        let rsum_m_prime_plus_total_eps = cadd(&mut d, p, rsum_m_prime, total_eps);
        let upper_ty = cle(&mut d, p, rsum_m_prime, rsum_m_plus_total_eps);
        let lower_ty = cle(&mut d, p, rsum_m, rsum_m_prime_plus_total_eps);
        let logic = p.rat.int.logic;
        let expected = d.const_app(logic.and, &[upper_ty, lower_ty]);

        let ty = {
            let after_hge = d.arrow(hge_ty, expected);
            d.arrow(hab_ty, after_hge)
        };
        let value = {
            let with_hge = d.lam_fv(hge_fv, hge_ty, applied);
            d.lam_fv(hab_fv, hab_ty, with_hge)
        };

        let anon = d.kernel().anon();
        let name_ok = d
            .kernel()
            .name_str(anon, "__riemannSumReblockCloseConcreteOk");
        let result_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: name_ok,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result_ok.is_ok(),
            "riemann_sum_reblock_close at (identity, 0, 1, e=0, m=2, n=1) \
             must have the expected conclusion type: {:?}",
            result_ok.err()
        );

        // Negative control: swap `total_eps` for the UNDOUBLED `eps_term`.
        let rsum_m_plus_eps_term = cadd(&mut d, p, rsum_m, eps_term);
        let rsum_m_prime_plus_eps_term = cadd(&mut d, p, rsum_m_prime, eps_term);
        let wrong_upper_ty = cle(&mut d, p, rsum_m_prime, rsum_m_plus_eps_term);
        let wrong_lower_ty = cle(&mut d, p, rsum_m, rsum_m_prime_plus_eps_term);
        let wrong_expected = d.const_app(logic.and, &[wrong_upper_ty, wrong_lower_ty]);
        let wrong_ty = {
            let after_hge = d.arrow(hge_ty, wrong_expected);
            d.arrow(hab_ty, after_hge)
        };
        let wrong_value = {
            let with_hge = d.lam_fv(hge_fv, hge_ty, applied);
            d.lam_fv(hab_fv, hab_ty, with_hge)
        };
        let name_bad = d
            .kernel()
            .name_str(anon, "__riemannSumReblockCloseConcreteBad");
        let result_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_bad,
            uparams: vec![],
            ty: wrong_ty,
            value: wrong_value,
        });
        assert!(
            result_bad.is_err(),
            "the SAME proof must be REFUSED against a conclusion using the \
             UNDOUBLED epsTerm instead of totalEps"
        );
    }
}

// --- roadmap step 5: `riemannSum_cauchy`, closing the roadmap --------------

/// `Equiv (add (add a b) (neg a)) b` — the group cancellation `(a+b)+(−a) ~
/// b`. A verbatim, private restatement of `series.rs`'s own private
/// `cancel_right` — `creal::integral` and `creal::series` are siblings, not
/// descendants of each other, so the Rust-private original is not visible
/// here (see `ring_helpers.rs`'s own module documentation for why this
/// repository duplicates small ring-algebra helpers per-file rather than
/// promoting every one of them to a shared module).
fn cancel_right(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let ab = cadd(d, p, a, b);
    let start = cadd(d, p, ab, na);

    // (a+b)+(-a) ~ (b+a)+(-a)
    let ba = cadd(d, p, b, a);
    let comm1 = d.lemma(p.add_comm, &[a, b]);
    let refl_na = d.lemma(p.equiv_refl, &[na]);
    let s1 = cadd(d, p, ba, na);
    let h1 = d.lemma(p.add_congr, &[ab, ba, na, na, comm1, refl_na]);

    // (b+a)+(-a) ~ b+(a+(-a))
    let a_na = cadd(d, p, a, na);
    let s2 = cadd(d, p, b, a_na);
    let h2 = d.lemma(p.add_assoc, &[b, a, na]);

    // b+(a+(-a)) ~ b+zero
    let zero_c = czero(d, p);
    let h_an = d.lemma(p.add_neg, &[a]);
    let refl_b = d.lemma(p.equiv_refl, &[b]);
    let s3 = cadd(d, p, b, zero_c);
    let h3 = d.lemma(p.add_congr, &[b, b, a_na, zero_c, refl_b, h_an]);

    // b+zero ~ b
    let h4 = d.lemma(p.add_zero, &[b]);

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (b, h4)])
}

/// `Equiv (neg (add a (neg b))) (add b (neg a))` — the CReal-level sign-flip
/// identity [`declare_riemann_sum_cauchy`] needs to read the SAME `t := add
/// a (neg b)` on both sides of [`CRealPrelude::within_of_two_sided_le`]'s
/// two hypotheses: that lemma needs `le t y` and `le (neg t) y`, but the two
/// `le` facts `riemannSum_reblock_close`'s `And` conclusion actually
/// supplies rearrange most directly into `le (add a (neg b)) y` and `le (add
/// b (neg a)) y` — the same pair up to THIS identity, not up to `neg`
/// applied to the first.
///
/// `CReal.neg` takes **no** index shift (`declare_negation`'s own
/// definition, `neg x := mk (fun n => Rat.neg (seq x n)) _`), so both sides
/// sample `a`/`b` at the identical shifted index on every `n`, and the whole
/// identity is one `Rat.neg_sub` application per index via
/// `Equiv.of_pointwise` — no CReal-level ring lemma needed, exactly the
/// pattern `declare_additive_laws`'s own `add_comm`/`add_neg` pointwise
/// proofs already use one section up in this same file.
fn neg_sub_symm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let rat = p.rat;
    let nat = d.nat_ty();

    let neg_b = cneg(d, p, b);
    let a_neg_b = cadd(d, p, a, neg_b);
    let left = cneg(d, p, a_neg_b);

    let neg_a = cneg(d, p, a);
    let right = cadd(d, p, b, neg_a);

    let pointwise = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let index = shift(d, n);
        let sa = sample(d, p, a, index);
        let sb = sample(d, p, b, index);
        let body = d.lemma(rat.neg_sub, &[sa, sb]);
        d.lam_fv(n_fv, nat, body)
    };
    d.lemma(p.equiv_of_pointwise, &[left, right, pointwise])
}

/// `CReal.riemannSum_cauchy : ∀ F a b e n k, le a b →
/// UniformlyContinuousOn F a b → ∀ i : Nat, Within (seq (add (riemannSum F a
/// b m_prime) (neg (riemannSum F a b m))) i) (add (seq totalEps i)
/// (natDivSucc 2 i))`, `m := Nat.add deep k` (`deep`
/// [`declare_riemann_sum_reblock_close`]'s own Archimedean threshold at `(F,
/// a, b, e, u)`; `k` an arbitrary extra depth, discharging `Nat.le deep m`
/// unconditionally via `Nat.le_add_right` rather than leaving it an assumed
/// hypothesis, the way `riemann_sum_reblock_close`'s own tests do), `m_prime`/
/// `totalEps` [`declare_riemann_sum_reblock_close`]'s own witness and error
/// term at that `m`.
///
/// Roadmap step 5, closing the roadmap `riemannSum_reblock_close`'s own doc
/// comment opens: rearrange its two-sided `≤` sandwich (`le rsum_m_prime (add
/// rsum_m totalEps)`, `le rsum_m (add rsum_m_prime totalEps)`) into the
/// two-sided form [`CRealPrelude::within_of_two_sided_le`] itself demands
/// (`le t totalEps`, `le (neg t) totalEps` at the SAME `t := add rsum_m_prime
/// (neg rsum_m)`) via [`cancel_right`] on each half and [`neg_sub_symm`] to
/// bridge the second half's `add rsum_m (neg rsum_m_prime)` shape over to
/// `neg t`, then apply `within_of_two_sided_le` directly — its own
/// conclusion is already the `∀ i, Within …` Pi this declaration's own type
/// states, so no further index-introduction is needed.
///
/// **This is not `CReal.Cauchy (fun m => riemannSum F a b m)` in that
/// definition's own literal shape** (`∃ K, ∀ m n, Within (seq (f m) m − seq
/// (f n) n) (natDivSucc K m + natDivSucc K n)`, comparing samples at each
/// term's OWN canonical index). Reaching that shape needs the
/// representative-index bridging telescope `series.rs`'s own module
/// documentation measures, for the structurally analogous `sumRange` case,
/// at 35–45 further proof-term steps (`declare_sum_range_cauchy_of_dominated`'s
/// whole derivation) — genuinely separate work, not attempted here. What
/// this theorem proves is the raw, unscaled closeness bound that content
/// would rest on: past the Archimedean threshold, any mesh count `m` and any
/// further `(Nat.succ n)`-fold common refinement `m_prime` of it produce
/// Riemann sums within `totalEps` of one another at EVERY rational sample
/// index `i`, up to the universal `2/(i+1)` bridging slack
/// `within_of_two_sided_le` itself always carries.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_cauchy(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let np = d.prelude();

    // `deep`, EXACTLY as `declare_riemann_sum_reblock_close` computes it.
    let width = width_of(d, p, a, b);
    let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let outer = d.apply(modulus_fn, &[e]);
    let (c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);
    let me = NatOps::mul(d, magnitude, outer);
    let deep = NatOps::add(d, me, c);

    // `m := deep + k`; `Nat.le deep m` unconditionally via `Nat.le_add_right`
    // — no assumed hypothesis, unlike `riemann_sum_reblock_close`'s own `hge`.
    let m = NatOps::add(d, deep, k);
    let hge = d.lemma(np.le_add_right, &[deep, k]);

    let and_result = d.lemma(
        p.riemann_sum_reblock_close,
        &[f, a, b, e, m, n, hab, u, hge],
    );

    let (m_prime, _succ_proof) = succ_mul_succ(d, n, m);
    let rsum_m_prime = rsum(d, p, f, a, b, m_prime);
    let rsum_m = rsum(d, p, f, a, b, m);

    let delta_m = delta_of(d, p, a, b, m);
    let one_nat = d.num(1);
    let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let eps_embed = embed(d, p, eps_rat);
    let eps_term = cmul(d, p, eps_embed, delta_m);
    let sm = d.succ(m);
    let sm_real = d.const_app(p.of_nat, &[sm]);
    let total_eps = cmul(d, p, sm_real, eps_term);

    let rsum_m_plus_total_eps = cadd(d, p, rsum_m, total_eps);
    let rsum_m_prime_plus_total_eps = cadd(d, p, rsum_m_prime, total_eps);
    let upper_ty = cle(d, p, rsum_m_prime, rsum_m_plus_total_eps);
    let lower_ty = cle(d, p, rsum_m, rsum_m_prime_plus_total_eps);
    let logic = p.rat.int.logic;
    let upper = d.const_app(logic.and_left, &[upper_ty, lower_ty, and_result]);
    let lower = d.const_app(logic.and_right, &[upper_ty, lower_ty, and_result]);

    // t := add rsum_m_prime (neg rsum_m).
    let neg_rsum_m = cneg(d, p, rsum_m);
    let t = cadd(d, p, rsum_m_prime, neg_rsum_m);

    // h1 : le t total_eps, from `upper : le rsum_m_prime rsum_m_plus_total_eps`
    // via `add_le_add` (add `neg rsum_m` to both sides) then `cancel_right`
    // (`(rsum_m + total_eps) + (neg rsum_m) ~ total_eps`).
    let h1 = {
        let refl_neg = d.lemma(p.le_refl, &[neg_rsum_m]);
        let rhs_added = cadd(d, p, rsum_m_plus_total_eps, neg_rsum_m);
        let step_added = d.lemma(
            p.add_le_add,
            &[
                rsum_m_prime,
                rsum_m_plus_total_eps,
                neg_rsum_m,
                neg_rsum_m,
                upper,
                refl_neg,
            ],
        );
        // step_added : le t rhs_added
        let cancel_eq = cancel_right(d, p, rsum_m, total_eps);
        // cancel_eq : Equiv rhs_added total_eps
        let refl_t = d.lemma(p.equiv_refl, &[t]);
        d.lemma(
            p.le_congr,
            &[t, t, rhs_added, total_eps, refl_t, cancel_eq, step_added],
        )
    };

    // h2 : le (neg t) total_eps, from `lower : le rsum_m
    // rsum_m_prime_plus_total_eps` the same way, then bridged across
    // `neg_sub_symm` from `add rsum_m (neg rsum_m_prime)` to `neg t`.
    let neg_rsum_m_prime = cneg(d, p, rsum_m_prime);
    let lhs2 = cadd(d, p, rsum_m, neg_rsum_m_prime);
    let h2_prime = {
        let refl_neg_prime = d.lemma(p.le_refl, &[neg_rsum_m_prime]);
        let rhs_added = cadd(d, p, rsum_m_prime_plus_total_eps, neg_rsum_m_prime);
        let step_added = d.lemma(
            p.add_le_add,
            &[
                rsum_m,
                rsum_m_prime_plus_total_eps,
                neg_rsum_m_prime,
                neg_rsum_m_prime,
                lower,
                refl_neg_prime,
            ],
        );
        // step_added : le lhs2 rhs_added
        let cancel_eq = cancel_right(d, p, rsum_m_prime, total_eps);
        // cancel_eq : Equiv rhs_added total_eps
        let refl_lhs2 = d.lemma(p.equiv_refl, &[lhs2]);
        d.lemma(
            p.le_congr,
            &[
                lhs2, lhs2, rhs_added, total_eps, refl_lhs2, cancel_eq, step_added,
            ],
        )
    };
    let neg_t = cneg(d, p, t);
    let bridge = neg_sub_symm(d, p, rsum_m_prime, rsum_m);
    // bridge : Equiv neg_t lhs2
    let bridge_symm = d.lemma(p.equiv_symm, &[neg_t, lhs2, bridge]);
    // bridge_symm : Equiv lhs2 neg_t
    let refl_total_eps = d.lemma(p.equiv_refl, &[total_eps]);
    let h2 = d.lemma(
        p.le_congr,
        &[
            lhs2,
            neg_t,
            total_eps,
            total_eps,
            bridge_symm,
            refl_total_eps,
            h2_prime,
        ],
    );

    // proof_body : ∀ i, Within (seq t i) (add (seq total_eps i) (natDivSucc 2 i))
    let proof_body = d.lemma(p.within_of_two_sided_le, &[t, total_eps, h1, h2]);

    let conclusion_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let seq_t_i = sample(d, p, t, i);
        let seq_y_i = sample(d, p, total_eps, i);
        let slack = div_succ(d, p, 2, i);
        let bound = radd(d, seq_y_i, slack);
        let claim = within(d, p, seq_t_i, bound);
        d.pi_fv(i_fv, nat, claim)
    };

    let ty = {
        let after_u = d.pi_fv(u_fv, u_ty, conclusion_ty);
        let after_hab = d.arrow(hab_ty, after_u);
        let over_k = d.pi_fv(k_fv, nat, after_hab);
        let over_n = d.pi_fv(n_fv, nat, over_k);
        let over_e = d.pi_fv(e_fv, nat, over_n);
        let over_b = d.pi_fv(b_fv, carrier, over_e);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_u = d.lam_fv(u_fv, u_ty, proof_body);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_k = d.lam_fv(k_fv, nat, with_hab);
        let over_n = d.lam_fv(n_fv, nat, over_k);
        let over_e = d.lam_fv(e_fv, nat, over_n);
        let over_b = d.lam_fv(b_fv, carrier, over_e);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_cauchy,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod riemann_sum_cauchy_tests {
    use super::*;
    use crate::Declaration;

    /// **Mandatory concrete instantiation, with a negative control.**
    /// `F := identity`, `a := ofNat 0`, `b := ofNat 1`, `e := 0`, `n := 1`,
    /// `k := 0` (i.e. `m := deep` exactly — `k` is kept as a genuine free
    /// parameter of the DECLARATION, not fixed to `0` there, but `0` is
    /// deliberately the smallest instantiation here: `m` and `m_prime` drive
    /// nested `sumRange`/`Nat.mul` unfoldings over UNARY `Nat`s, and `k := 3`
    /// was measured to still be running after 669s of pure CPU before being
    /// killed, against `riemann_sum_reblock_close`'s own concrete test's
    /// comparable `m := 2` — a real cost difference, not a hang). `hab` is
    /// left ASSUMED (a free hypothesis) — the same choice
    /// `riemann_sum_reblock_close`'s own concrete test makes, since proving
    /// it numerically needs `CReal.bound` computation this declaration's own
    /// TYPE does not need. `u := CReal.uniformly_continuous_id a b` is a REAL
    /// witness, not a placeholder.
    ///
    /// The negative control swaps `total_eps` for the UNDOUBLED `eps_term`
    /// in the reconstructed bound — the same "forgot to multiply by the
    /// block count" bug `riemann_sum_reblock_close`'s own control catches.
    /// `sm = Nat.succ (deep + k)` is at least `2` regardless of `deep`'s own
    /// value (`CReal.bound` is `Int.natAbs (…) + 1`, so `deep >= 1` and
    /// `sm >= 2` even at `k := 0`), so `total_eps` (`sm` copies of
    /// `eps_term`) and the bare `eps_term` are genuinely different `CReal`
    /// literals here, not a vacuous relabeling.
    #[test]
    fn riemann_sum_cauchy_applies_at_concrete_literals() {
        crate::on_a_deep_stack(riemann_sum_cauchy_concrete_body);
    }

    fn riemann_sum_cauchy_concrete_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);
        let nat = d.nat_ty();

        let identity = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            d.lam_fv(x_fv, carrier, x)
        };

        let zero_nat = d.num(0);
        let one_nat_lit = d.num(1);
        let a = d.const_app(p.of_nat, &[zero_nat]);
        let b = d.const_app(p.of_nat, &[one_nat_lit]);
        let e = d.num(0);
        let n = d.num(1);
        let k = d.num(0);

        let u = d.const_app(p.uniformly_continuous_id, &[a, b]);

        let hab_ty = cle(&mut d, p, a, b);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);

        let applied = d.const_app(p.riemann_sum_cauchy, &[identity, a, b, e, n, k, hab, u]);

        // Independently reconstruct `m`, `t`, `total_eps`, exactly the way
        // the real declaration computes them.
        let modulus_fn = d.const_app(p.uc_modulus, &[identity, a, b, u]);
        let outer = d.apply(modulus_fn, &[e]);
        let width = width_of(&mut d, p, a, b);
        let (c, magnitude, _width_le_mag) = direct_bound_le(&mut d, p, width);
        let me = NatOps::mul(&mut d, magnitude, outer);
        let deep = NatOps::add(&mut d, me, c);
        let m = NatOps::add(&mut d, deep, k);

        let (m_prime, _succ_proof) = succ_mul_succ(&mut d, n, m);
        let rsum_m_prime = rsum(&mut d, p, identity, a, b, m_prime);
        let rsum_m = rsum(&mut d, p, identity, a, b, m);

        let delta_m = delta_of(&mut d, p, a, b, m);
        let one_nat = d.num(1);
        let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
        let eps_embed = embed(&mut d, p, eps_rat);
        let eps_term = cmul(&mut d, p, eps_embed, delta_m);
        let sm = d.succ(m);
        let sm_real = d.const_app(p.of_nat, &[sm]);
        let total_eps = cmul(&mut d, p, sm_real, eps_term);

        let neg_rsum_m = cneg(&mut d, p, rsum_m);
        let t = cadd(&mut d, p, rsum_m_prime, neg_rsum_m);

        let conclusion_ty_ok = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let seq_t_i = sample(&mut d, p, t, i);
            let seq_y_i = sample(&mut d, p, total_eps, i);
            let slack = div_succ(&mut d, p, 2, i);
            let bound = radd(&mut d, seq_y_i, slack);
            let claim = within(&mut d, p, seq_t_i, bound);
            d.pi_fv(i_fv, nat, claim)
        };
        let ty_ok = d.arrow(hab_ty, conclusion_ty_ok);
        let value_ok = d.lam_fv(hab_fv, hab_ty, applied);

        let anon = d.kernel().anon();
        let name_ok = d.kernel().name_str(anon, "__riemannSumCauchyConcreteOk");
        let result_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: name_ok,
            uparams: vec![],
            ty: ty_ok,
            value: value_ok,
        });
        assert!(
            result_ok.is_ok(),
            "riemann_sum_cauchy at (identity, 0, 1, e=0, n=1, k=3) must have \
             the expected `Within`-shaped conclusion type: {:?}",
            result_ok.err()
        );

        // Negative control: swap `total_eps` for the UNDOUBLED `eps_term`.
        let conclusion_ty_bad = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let seq_t_i = sample(&mut d, p, t, i);
            let seq_y_i = sample(&mut d, p, eps_term, i);
            let slack = div_succ(&mut d, p, 2, i);
            let bound = radd(&mut d, seq_y_i, slack);
            let claim = within(&mut d, p, seq_t_i, bound);
            d.pi_fv(i_fv, nat, claim)
        };
        let ty_bad = d.arrow(hab_ty, conclusion_ty_bad);
        let value_bad = d.lam_fv(hab_fv, hab_ty, applied);

        let name_bad = d.kernel().name_str(anon, "__riemannSumCauchyConcreteBad");
        let result_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_bad,
            uparams: vec![],
            ty: ty_bad,
            value: value_bad,
        });
        assert!(
            result_bad.is_err(),
            "the SAME proof must be REFUSED against a conclusion using the \
             UNDOUBLED eps_term instead of total_eps"
        );
    }
}

// --- the representative-index bridge -- shared-index closeness implies
// own-canonical-index closeness, the one gap `riemannSum_cauchy`'s own doc
// comment names between it and `CReal.integral`. -----------------------------

/// `CReal.sharedIndexToCanonical : ∀ (X Y : CReal) (bound : Nat → Rat),
/// (∀ i, Within (seq (add X (neg Y)) i) (bound i)) → ∀ p q j : Nat,
/// Within (Rat.sub (seq X p) (seq Y q))
///        ((modulus p (shift j) + bound j) + modulus (shift j) q)`.
///
/// **The representative-index bridge.** `riemannSum_cauchy` (and, per this
/// module's own top-of-file documentation, `series.rs`'s structurally
/// analogous `sumRange` case) proves closeness of a `CReal` difference `t :=
/// add X (neg Y)` at an arbitrary SHARED index `i` — `seq t i`, which by
/// `add`/`neg`'s own definitions (`add x y := mk (fun n => x_(2n+1) +
/// y_(2n+1))`, `neg x := mk (fun n => Rat.neg (x_n))`, `declare_addition`/
/// `declare_negation` in `creal.rs`) is `seq X (shift i) − seq Y (shift i)`,
/// the SAME shifted index on both sides. `CReal.RegularSeq`/`CReal.Cauchy`
/// instead compare `X` and `Y` at their OWN, generally DIFFERENT, canonical
/// indices `p`/`q` — `seq X p − seq Y q`. Those are not the same quantity,
/// and nothing in `riemannSum_cauchy`'s own statement bridges them.
///
/// This theorem is that bridge. Given any auxiliary index `j`, `seq X p −
/// seq Y q` telescopes through `seq X (shift j)` and `seq Y (shift j)` via
/// [`chain_within3`] — three legs:
///
/// 1. `seq X p − seq X (shift j)`, bounded by `X`'s own
///    [`CRealPrelude::regular`] at `(p, shift j)` — every `CReal` is regular
///    against ITSELF at any two indices, the same accessor
///    [`super::completeness`]'s own module documentation already reads this
///    way ("the sample each real already offers at its own index ... is
///    equivalent up to a constant factor to bounding `X` ... as a real");
/// 2. `seq X (shift j) − seq Y (shift j)`, exactly `H` read at `j` — DEFEQ to
///    the stated middle-leg shape via unfolding `add`/`neg`/`Rat.sub` plus
///    beta reduction, the same "ordinary ... defeq" pattern
///    [`declare_riemann_sum_const`] already uses, with no bridging lemma
///    needed;
/// 3. `seq Y (shift j) − seq Y q`, bounded by `Y`'s own `regular` at
///    `(shift j, q)`.
///
/// **Genuinely reusable, not `riemannSum`-specific**: `X`, `Y` and `bound`
/// are all free parameters, and nothing in the statement or proof mentions
/// `riemannSum`/`sumRange`. The same theorem closes the analogous
/// representative-index gap `series.rs`'s own module documentation measures
/// for `CReal.sumRange_cauchy_of_dominated`'s shared-index estimates.
///
/// **Does not by itself produce `RegularSeq`/`Cauchy`**, and so does not by
/// itself reach `CReal.integral`. [`common_refinement`] (this file, right
/// after [`succ_mul_succ`]) is the construction this doc comment used to
/// call "separate, unattempted work": given two ARBITRARY, otherwise
/// unrelated `Nat` counts `m1, m2`, it builds the shared refinement target
/// `l` both `succ_mul_succ(m2, m1)` and `succ_mul_succ(m1, m2)` land on,
/// identifying the two via `Nat.mul_comm` plus one additive reassociation.
/// It is landed and kernel-verified, both symbolically (the load-bearing
/// check — see its own doc comment for why a CONCRETE instantiation cannot
/// exercise the commutation bug at all) and with a genuine proof-term-level
/// negative control.
///
/// **That construction is necessary but not sufficient, and the reason is
/// worth stating precisely because it changes WHICH sequence
/// `CReal.integral` has to be built from.** `riemannSum_cauchy`'s bound
/// (`total_eps`, this file's own computation inside
/// [`declare_riemann_sum_cauchy`]) is `width/(e+1)` — a function of the
/// chosen ACCURACY `e`, and INDEPENDENT of the subinterval count `m` itself
/// (`m` only has to satisfy `m = deep(e) + k` for some `k ≥ 0`, i.e. "deep
/// enough for `e`"). `CReal.RegularSeq`/`Cauchy` demand a bound that shrinks
/// as a function of the SEQUENCE'S OWN index — `natDivSucc K p +
/// natDivSucc K q` for a FIXED `K`, i.e. rate exactly `O(1/p)`. For the
/// LITERAL raw-indexed sequence `fun n => riemannSum F a b n`, matching
/// these two requires choosing `e` as a function of the outer index `p`
/// itself while keeping `deep(e) ≤ p` — i.e. INVERTING `deep`, which is
/// built from `CReal.UniformlyContinuousOn`'s `modulus : Nat → Nat` field
/// (`uniform_continuity.rs`'s own carrier declaration: fully general, no
/// growth constraint). This is the SAME class of obstruction
/// `uniform_continuity.rs`'s own module documentation already names and
/// declines to build for a different bridge
/// (`uniformly_continuous_imp_continuous_at`: "a genuine `Nat`-division
/// search ... not a rearrangement"), not a new one — and for an arbitrary
/// modulus, no fixed `K` need exist at all: if `deep` grows faster than
/// linearly, the best achievable rate at index `p` is slower than `O(1/p)`,
/// which no choice of `K` can dominate.
///
/// **The fix is to reindex, not to invert.** Define `Y(n) := riemannSum F a
/// b (deep(f, a, b, u, n) + 0)` (`deep` computed by the SAME `width_of` /
/// `uc_modulus` / [`direct_bound_le`] / `NatOps::mul`/`add` recipe
/// [`declare_riemann_sum_cauchy`] already builds inline — see that
/// declaration's own test module for the precedent of reconstructing this
/// EXTERNALLY, term-for-term, so the kernel sees the same expression rather
/// than needing a bridging lemma). Now `e := n` directly (no inversion), and
/// `RegularSeq Y`'s two arbitrary indices `p, q` become two arbitrary `Nat`s
/// `m1 := deep(p)+0`, `m2 := deep(q)+0` fed straight into
/// [`common_refinement`] — exactly the shape that construction was built
/// for. The full route: `riemannSum_cauchy` twice (`e:=p, n_refine:=m2` and
/// `e:=q, n_refine:=m1`), [`crate::rat_prelude::ops::nat_rewrite_prop`] once
/// (aligning the second call's refinement target onto `common_refinement`'s
/// `l`, since the first call already lands there with no rewrite needed),
/// [`declare_shared_index_to_canonical`] twice (`jj := p` and `jj := q`
/// respectively resolves every remaining term to the right `O(1/p)`/`O(1/q)`
/// shape), and `series.rs`'s `within_symm` plus one `Rat.bounds_add`/
/// `Rat.sub_add_sub` step (`chain_within3`'s own first fuse, one leg
/// shorter) to combine the two three-leg outputs into a single `p`-vs-`q`
/// bound.
///
/// **What is STILL missing, sized precisely rather than gestured at:**
/// every piece above produces a bound that MENTIONS `seq(total_eps) j` —
/// the sample of a CONCRETE `CReal` (`total_eps`, built from `ofNat`, `mul`,
/// and an embedded rational), not yet a closed-form rational. Turning that
/// into a genuine `K/(index+1)` bound needs its own short lemma: `total_eps
/// ~ mul(width, embed(natDivSucc 1 e))` (an `Equiv`, via the ALREADY-PROVED
/// [`declare_riemann_sum_const`]'s own `mesh_inverse_identity` plus
/// `mul_assoc`/`mul_comm`/`mul_congr` ring rewriting — the exact same
/// "eight-step associativity/commutativity rewrite" that declaration already
/// performs, at a different target), and then one sample-closeness bridge
/// from that `Equiv` to a rational bound on `width`'s own magnitude (via
/// [`direct_bound_le`], already used for exactly this purpose elsewhere in
/// this file). This is a genuinely new, self-contained sub-lemma — comparable
/// in size to [`direct_bound_le`] itself, not a rearrangement of existing
/// pieces — and is the actual remaining gate on `CReal.integral`, not the
/// common-refinement construction this doc comment used to point at.
///
/// Once that bound exists, `CReal.integral` should be built via
/// `CReal.regular_of_scaled_cauchy`/`CReal.mk` on `speedup(diagonal Y, K)`
/// (`convergence.rs`), NOT `completeness.rs`'s `CReal.limit`: the scaled
/// form takes exactly the `natDivSucc K m + natDivSucc K n` shape this
/// construction produces directly, while `CReal.limit` needs the EXACT
/// modulus `1/(m+1)+1/(n+1)` with no slack, which would need an additional
/// [`weaken`](super::weaken) step this route does not.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_shared_index_to_canonical(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rat = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let bound_fv = d.fresh_fvar();
    let bound = d.kernel().fvar(bound_fv);
    let bound_ty = d.arrow(nat, rat);

    // t := add X (neg Y).
    let neg_y = cneg(d, p, y);
    let t = cadd(d, p, x, neg_y);

    let h_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let seq_t_i = sample(d, p, t, i);
        let bound_i = d.apply(bound, &[i]);
        let claim = within(d, p, seq_t_i, bound_i);
        d.pi_fv(i_fv, nat, claim)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let qq_fv = d.fresh_fvar();
    let qq = d.kernel().fvar(qq_fv);
    let jj_fv = d.fresh_fvar();
    let jj = d.kernel().fvar(jj_fv);

    let conclusion_ty = {
        let sj = shift(d, jj);
        let seq_x_pp = sample(d, p, x, pp);
        let seq_y_qq = sample(d, p, y, qq);
        let diff = rsub(d, p.rat, seq_x_pp, seq_y_qq);
        let leg1 = modulus(d, p, pp, sj);
        let bound_j = d.apply(bound, &[jj]);
        let leg12 = radd(d, leg1, bound_j);
        let leg3 = modulus(d, p, sj, qq);
        let total = radd(d, leg12, leg3);
        within(d, p, diff, total)
    };

    let ty = {
        let after_jj = d.pi_fv(jj_fv, nat, conclusion_ty);
        let after_qq = d.pi_fv(qq_fv, nat, after_jj);
        let after_pp = d.pi_fv(pp_fv, nat, after_qq);
        let after_h = d.arrow(h_ty, after_pp);
        let after_bound = d.pi_fv(bound_fv, bound_ty, after_h);
        let after_y = d.pi_fv(y_fv, carrier, after_bound);
        d.pi_fv(x_fv, carrier, after_y)
    };

    let value_body = {
        let sj = shift(d, jj);
        let seq_x_pp = sample(d, p, x, pp);
        let seq_x_sj = sample(d, p, x, sj);
        let seq_y_sj = sample(d, p, y, sj);
        let seq_y_qq = sample(d, p, y, qq);

        let bxy = modulus(d, p, pp, sj);
        let byz = d.apply(bound, &[jj]);
        let bzw = modulus(d, p, sj, qq);

        let pxy = d.lemma(p.regular, &[x, pp, sj]);
        let pyz = d.apply(h, &[jj]);
        let pzw = d.lemma(p.regular, &[y, sj, qq]);

        chain_within3(
            d, p, seq_x_pp, seq_x_sj, seq_y_sj, seq_y_qq, bxy, byz, bzw, pxy, pyz, pzw,
        )
    };

    let value = {
        let with_jj = d.lam_fv(jj_fv, nat, value_body);
        let with_qq = d.lam_fv(qq_fv, nat, with_jj);
        let with_pp = d.lam_fv(pp_fv, nat, with_qq);
        let with_h = d.lam_fv(h_fv, h_ty, with_pp);
        let with_bound = d.lam_fv(bound_fv, bound_ty, with_h);
        let with_y = d.lam_fv(y_fv, carrier, with_bound);
        d.lam_fv(x_fv, carrier, with_y)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.shared_index_to_canonical,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod shared_index_to_canonical_tests {
    use super::*;
    use crate::Declaration;

    /// **Mandatory concrete instantiation, with a negative control.**
    /// `X := zero`, `Y := one` (genuinely different reals — the negative
    /// control below needs `X`/`Y` unrelated by `regular` alone, and `zero`/
    /// `one` are PRIMITIVE `CReal` constants, not built via `ofNat`'s
    /// `Nat`-recursive definition — measured: instantiating this same test
    /// at `ofNat 5`/`ofNat 2` did not finish `add_declaration`'s defeq check
    /// within 300s, where `zero`/`one` finish in seconds. This matches
    /// `riemann_sum_cauchy`'s own concrete test picking the SMALLEST
    /// instantiation available for exactly this reason), `bound := fun _ =>
    /// natDivSucc 2 0` (the constant `2`), `p := q := j := 6` — concrete
    /// `Nat`s large enough that `X`/`Y`'s own [`CRealPrelude::regular`] legs
    /// (`modulus 6 13 ≈ 0.214` each, `shift 6 = 13`) are individually too
    /// small to bound `|seq X 6 − seq Y 6| = 1` without the middle leg's `2`
    /// — see the negative control below for why that inequality is exactly
    /// the point. `H` is left ASSUMED (a free hypothesis), the same choice
    /// `riemann_sum_cauchy`'s own concrete test makes for `hab`: proving `H`
    /// itself needs no arithmetic this theorem's own statement does not
    /// need, and this test is about the BRIDGE'S telescope shape, not about
    /// producing a witness for an arbitrary hypothesis.
    ///
    /// The negative control drops the MIDDLE leg (`H`'s own contribution)
    /// from the reconstructed bound — the same "forgot a term" bug shape
    /// [`declare_riemann_sum_cauchy`]'s own test catches for `total_eps`.
    /// **Not vacuous, and genuinely false, not just differently-shaped**:
    /// `modulus 6 13 + modulus 13 6 = 3/7 < 1 = |seq zero 6 − seq one 6|`, so
    /// the dropped-middle-leg statement is an actually-false `CReal.le`
    /// inequality over concrete rationals, refused on that basis, not merely
    /// on a syntactic mismatch a differently-associated but equally-true sum
    /// could paper over.
    #[test]
    fn shared_index_to_canonical_applies_at_concrete_literals() {
        crate::on_a_deep_stack(shared_index_to_canonical_concrete_body);
    }

    fn shared_index_to_canonical_concrete_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();

        let x = d.kernel().const_(p.zero, vec![]);
        let y = d.kernel().const_(p.one, vec![]);

        let two_nat = d.num(2);
        let zero_nat = d.num(0);
        let bound = {
            let ignored_fv = d.fresh_fvar();
            let real_body = d.const_app(p.rat.nat_div_succ, &[two_nat, zero_nat]);
            d.lam_fv(ignored_fv, nat, real_body)
        };

        let h_ty = {
            let neg_y = cneg(&mut d, p, y);
            let t = cadd(&mut d, p, x, neg_y);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let seq_t_i = sample(&mut d, p, t, i);
            let bound_i = d.apply(bound, &[i]);
            let claim = within(&mut d, p, seq_t_i, bound_i);
            d.pi_fv(i_fv, nat, claim)
        };
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let pp = d.num(6);
        let qq = d.num(6);
        let jj = d.num(6);

        let applied = d.const_app(p.shared_index_to_canonical, &[x, y, bound, h, pp, qq, jj]);

        let sj = shift(&mut d, jj);
        let seq_x_pp = sample(&mut d, p, x, pp);
        let seq_y_qq = sample(&mut d, p, y, qq);
        let diff = rsub(&mut d, p.rat, seq_x_pp, seq_y_qq);
        let leg1 = modulus(&mut d, p, pp, sj);
        let bound_j = d.apply(bound, &[jj]);
        let leg3 = modulus(&mut d, p, sj, qq);

        let ok_total = {
            let leg12 = radd(&mut d, leg1, bound_j);
            radd(&mut d, leg12, leg3)
        };
        let ok_ty = {
            let claim = within(&mut d, p, diff, ok_total);
            d.arrow(h_ty, claim)
        };
        let ok_value = d.lam_fv(h_fv, h_ty, applied);

        let anon = d.kernel().anon();
        let name_ok = d
            .kernel()
            .name_str(anon, "__sharedIndexToCanonicalConcreteOk");
        let result_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: name_ok,
            uparams: vec![],
            ty: ok_ty,
            value: ok_value,
        });
        assert!(
            result_ok.is_ok(),
            "sharedIndexToCanonical at (zero, one, p=6, q=6, j=6) must have \
             the expected three-leg `Within`-shaped conclusion type: {:?}",
            result_ok.err()
        );

        // Negative control: drop the middle leg (`bound j`) entirely.
        let bad_total = radd(&mut d, leg1, leg3);
        let bad_ty = {
            let claim = within(&mut d, p, diff, bad_total);
            d.arrow(h_ty, claim)
        };
        let bad_value = d.lam_fv(h_fv, h_ty, applied);

        let name_bad = d
            .kernel()
            .name_str(anon, "__sharedIndexToCanonicalConcreteBad");
        let result_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_bad,
            uparams: vec![],
            ty: bad_ty,
            value: bad_value,
        });
        assert!(
            result_bad.is_err(),
            "the SAME proof must be REFUSED against a conclusion that DROPS \
             the middle (`H`) leg from the reconstructed bound"
        );
    }
}

// --- `CReal.riemannSum_sharedAccuracyClose` -- the common-refinement
// construction wired together, for two counts sharing ONE accuracy `e`.
// See [`declare_shared_index_to_canonical`]'s own doc comment for exactly
// what this is (a real, self-contained step) and is not yet (literal
// `RegularSeq`/`Cauchy` for the raw-indexed sequence, which additionally
// needs reindexing via `deep` plus a new CReal-magnitude bound). ---------

/// `magnitude*outer + c` -- [`declare_riemann_sum_cauchy`]'s own internal
/// Archimedean depth `deep`, reconstructed EXTERNALLY term-for-term (same
/// `width_of`/`uc_modulus`/[`direct_bound_le`]/`NatOps::mul`/`add` calls, in
/// the same order) so that, after substitution, `riemann_sum_cauchy`'s
/// conclusion type at THESE `e`, `k` arguments computes exactly the `m1`/
/// `m2` this section builds -- no bridging lemma needed, the same idiom
/// `riemann_sum_cauchy`'s own concrete test already uses (see
/// [`riemann_sum_cauchy_tests`]'s doc comment for the precedent).
fn deep_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    u: ExprId,
    e: ExprId,
) -> ExprId {
    let width = width_of(d, p, a, b);
    let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let outer = d.apply(modulus_fn, &[e]);
    let (c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);
    let me = NatOps::mul(d, magnitude, outer);
    NatOps::add(d, me, c)
}

/// `seq(totalEps) i + natDivSucc 2 i`, `totalEps` built from `(a, b, e, m)`
/// EXACTLY the way [`declare_riemann_sum_cauchy`]'s own body computes it --
/// reconstructed here so [`declare_riemann_sum_shared_accuracy_close`] can
/// build the explicit `Nat -> Rat` bound function
/// [`CRealPrelude::shared_index_to_canonical`] needs, matching
/// `riemann_sum_cauchy`'s own conclusion by beta-reduction alone.
fn shared_accuracy_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    e: ExprId,
    m: ExprId,
    i: ExprId,
) -> ExprId {
    let delta_m = delta_of(d, p, a, b, m);
    let one_nat = d.num(1);
    let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let eps_embed = embed(d, p, eps_rat);
    let eps_term = cmul(d, p, eps_embed, delta_m);
    let sm = d.succ(m);
    let sm_real = d.const_app(p.of_nat, &[sm]);
    let total_eps = cmul(d, p, sm_real, eps_term);
    let seq_y_i = sample(d, p, total_eps, i);
    let slack = div_succ(d, p, 2, i);
    radd(d, seq_y_i, slack)
}

/// `fun i => shared_accuracy_bound(a, b, e, m, i)`, as an actual `Nat ->
/// Rat` term -- the explicit `bound` argument
/// [`CRealPrelude::shared_index_to_canonical`] takes.
fn shared_accuracy_bound_fn(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    e: ExprId,
    m: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = shared_accuracy_bound(d, p, a, b, e, m, i);
    d.lam_fv(i_fv, nat, body)
}

/// From `Within (x-y) bxy` and `Within (y-z) byz`, derive `Within (x-z)
/// (bxy+byz)` -- `series.rs`'s private `chain_within3`'s own FIRST fuse
/// step, one leg shorter (this file sees only that function's public
/// three-leg entry point, and this construction only ever has two legs to
/// combine, so it is reproduced directly rather than padded to three).
fn chain_within2(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    bxy: ExprId,
    byz: ExprId,
    pxy: ExprId,
    pyz: ExprId,
) -> ExprId {
    let rat = p.rat;
    let xy = rsub(d, rat, x, y);
    let yz = rsub(d, rat, y, z);
    let (lxy, rxy) = halves(d, p, xy, bxy, pxy);
    let (lyz, ryz) = halves(d, p, yz, byz, pyz);
    let combined = d.lemma(rat.bounds_add, &[xy, bxy, yz, byz, lxy, rxy, lyz, ryz]);
    let xy_plus_yz = radd(d, xy, yz);
    let xz = rsub(d, rat, x, z);
    let fuse = d.lemma(rat.sub_add_sub, &[x, y, z]);
    let bound = radd(d, bxy, byz);
    rat_eq_rewrite(d, xy_plus_yz, xz, fuse, combined, &|d, t| {
        within(d, p, t, bound)
    })
}

/// From `Within (a-b) bab` and `Within (c-e) bce`, derive `Within
/// ((a+c)-(b+e)) (bab+bce)` via `Rat.sub_add_add` -- combining TWO
/// INDEPENDENT deltas (unlike [`chain_within2`], which needs a SHARED
/// middle point `y`) into a bound on the sum/sum pair.
/// `declare_converges_add`'s own final combining step
/// (`convergence.rs`) runs exactly this identity inline; extracted here
/// since [`declare_riemann_sum_add_cauchy_cross`] needs it twice.
fn chain_within2_pair(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
    bab: ExprId,
    bce: ExprId,
    pab: ExprId,
    pce: ExprId,
) -> ExprId {
    let rat = p.rat;
    let ab = rsub(d, rat, a, b);
    let ce = rsub(d, rat, c, e);
    let (lab, rab) = halves(d, p, ab, bab, pab);
    let (lce, rce) = halves(d, p, ce, bce, pce);
    let combined = d.lemma(rat.bounds_add, &[ab, bab, ce, bce, lab, rab, lce, rce]);
    let sum_ac_be = radd(d, ab, ce);
    let ac = radd(d, a, c);
    let be = radd(d, b, e);
    let target = rsub(d, rat, ac, be);
    // `Rat.sub_add_add(x1,x2,y1,y2) : Eq ((x1+x2)-(y1+y2)) ((x1-y1)+(x2-y2))`
    // -- OPPOSITE direction from `sub_add_sub`'s `Eq ((x-y)+(y-z)) (x-z)`;
    // `declare_converges_add`'s own `split_final`/`rsymm` usage confirms this
    // convention empirically (`convergence.rs`).
    let fuse = d.lemma(rat.sub_add_add, &[a, c, b, e]);
    // fuse : Eq target sum_ac_be
    let fuse_symm = rsymm(d, target, sum_ac_be, fuse);
    // fuse_symm : Eq sum_ac_be target
    let bound = radd(d, bab, bce);
    rat_eq_rewrite(d, sum_ac_be, target, fuse_symm, combined, &|d, t| {
        within(d, p, t, bound)
    })
}

/// `Within (seq x (shift n) − seq x n) (natDivSucc 2 n)` -- a single real's
/// own regularity between its own index and Bishop's shift. A verbatim,
/// private restatement of `convergence.rs`'s own private
/// `shift_regular_bound`/`shift_regular_le` (`creal::integral` and
/// `creal::convergence` are siblings, not descendants of each other, so the
/// Rust-private originals are not visible here -- see `cancel_right`'s own
/// doc comment in this same file for the identical cross-sibling-module
/// situation).
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

/// `Within (seq x (shift n) − seq x n) (natDivSucc 2 n)`. See
/// [`shift_regular_le`]'s own doc comment for why this is rebuilt rather
/// than reused.
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

/// `Rat.le x (Rat.add x y)`, given `0 ≤ y` -- the "pad by a nonnegative
/// slack" step [`direct_bound_le`]'s own `target_le_sum` construction
/// already runs (`add_le_add` against `le_refl`/the nonneg witness, then
/// `add_zero` to trim the padded left side); extracted for reuse by
/// [`declare_riemann_sum_add_cauchy_cross`], which needs the SAME move
/// three times (once per function) to strip [`bnd_leg_plus_share_le`]'s
/// extra `natDivSucc(1,idx)` slack down to a bare `bnd_leg ≤
/// natDivSucc(K,idx)` before folding it into a larger telescope.
fn le_add_nonneg_right(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    y_nonneg: ExprId,
) -> ExprId {
    let rat = p.rat;
    let refl_x = d.lemma(rat.le_refl, &[x]);
    let zero = rzero(d, rat);
    let widened = d.lemma(rat.add_le_add, &[x, x, zero, y, refl_x, y_nonneg]);
    // widened : le (x+0) (x+y)
    let padded = radd(d, x, zero);
    let trim = d.lemma(rat.add_zero, &[x]);
    let sum = radd(d, x, y);
    rat_eq_rewrite(d, padded, x, trim, widened, &|d, t| rle(d, rat, t, sum))
}

/// `Π i, Within (sample (add x (neg y)) i) (bound.apply i)` -- the shared-
/// index closeness hypothesis [`CRealPrelude::shared_index_to_canonical`]
/// itself takes, factored out here so
/// [`declare_riemann_sum_shared_accuracy_close_at`] can build the same
/// hypothesis TYPE twice (once per `y`) without duplicating
/// [`declare_shared_index_to_canonical`]'s own `h_ty` construction verbatim.
fn shared_index_hyp_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    bound: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let neg_y = cneg(d, p, y);
    let t = cadd(d, p, x, neg_y);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let seq_t_i = sample(d, p, t, i);
    let bound_i = d.apply(bound, &[i]);
    let claim = within(d, p, seq_t_i, bound_i);
    d.pi_fv(i_fv, nat, claim)
}

/// The pure "wiring" step behind [`CRealPrelude::riemann_sum_shared_accuracy_close`]:
/// two applications of [`CRealPrelude::shared_index_to_canonical`] that
/// SHARE `l` as `x`'s own sample index, combined via [`chain_within2`] into
/// one bound on `sample(y1,oi) − sample(y2,oj)`.
///
/// **This is the generalization this module's own doc comment (the
/// "eleventh lane" entry, above [`rat_sub_add_cancel`]) names as missing**:
/// `riemannSum_sharedAccuracyClose`'s own conclusion used to bake `l :=
/// common_refinement(m1,m2).0` in as a fixed subterm rather than exposing it
/// as a free parameter the way `shared_index_to_canonical` exposes `pp`.
/// Here `l`, `h1`, `h2`, `x`, `y1`, `y2`, `bound1_fn`, `bound2_fn` are all
/// free parameters -- nothing about `f`, `a`, `b`, `hab`, `u`, `k1`, `k2`, or
/// `riemannSum_cauchy`/`common_refinement` appears in this function at all.
/// [`declare_riemann_sum_shared_accuracy_close`] (the specialized version,
/// which still derives `l`/`h1`/`h2` internally via `riemann_sum_cauchy` +
/// [`common_refinement`]) now calls this directly, so its own proof is
/// LITERALLY built by this general construction rather than a hand-copy of
/// it; [`declare_riemann_sum_shared_accuracy_close_at`] exposes the same
/// construction as its own kernel-checked theorem, with `l`, `h1`, `h2`
/// genuinely `Π`-bound rather than internally derived.
///
/// Returns `(proof, bound)`, `proof : Within (sub (sample y1 oi) (sample y2
/// oj)) bound`.
#[allow(clippy::too_many_arguments)]
fn shared_accuracy_close_at_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y1: ExprId,
    y2: ExprId,
    bound1_fn: ExprId,
    bound2_fn: ExprId,
    l: ExprId,
    h1: ExprId,
    h2: ExprId,
    oi: ExprId,
    oj: ExprId,
    jj1: ExprId,
    jj2: ExprId,
) -> (ExprId, ExprId) {
    let app1 = d.lemma(
        p.shared_index_to_canonical,
        &[x, y1, bound1_fn, h1, l, oi, jj1],
    );
    let app2 = d.lemma(
        p.shared_index_to_canonical,
        &[x, y2, bound2_fn, h2, l, oj, jj2],
    );

    let b_val = sample(d, p, x, l);
    let a_val = sample(d, p, y1, oi);
    let c_val = sample(d, p, y2, oj);

    let shift_jj1 = shift(d, jj1);
    let m_l_sj1 = modulus(d, p, l, shift_jj1);
    let bound1_jj1 = d.apply(bound1_fn, &[jj1]);
    let m_sj1_oi = modulus(d, p, shift_jj1, oi);
    let m_l_sj1_plus_bound1 = radd(d, m_l_sj1, bound1_jj1);
    let bnd1 = radd(d, m_l_sj1_plus_bound1, m_sj1_oi);

    let shift_jj2 = shift(d, jj2);
    let m_l_sj2 = modulus(d, p, l, shift_jj2);
    let bound2_jj2 = d.apply(bound2_fn, &[jj2]);
    let m_sj2_oj = modulus(d, p, shift_jj2, oj);
    let m_l_sj2_plus_bound2 = radd(d, m_l_sj2, bound2_jj2);
    let bnd2 = radd(d, m_l_sj2_plus_bound2, m_sj2_oj);

    let app1_symm = within_symm(d, p, b_val, a_val, bnd1, app1);
    let final_proof = chain_within2(d, p, a_val, b_val, c_val, bnd1, bnd2, app1_symm, app2);

    let final_bound = radd(d, bnd1, bnd2);
    (final_proof, final_bound)
}

/// `CReal.riemannSum_sharedAccuracyClose_at`. See
/// [`shared_accuracy_close_at_proof`]'s own doc comment for the full
/// generalization this exposes at the kernel level: `l` (the shared
/// mid-anchor sample index) and the two closeness hypotheses `h1`/`h2` are
/// genuinely `Π`-bound parameters here, not internally derived from
/// `riemann_sum_cauchy`/`common_refinement` the way
/// [`CRealPrelude::riemann_sum_shared_accuracy_close`] derives them.
///
/// `CReal.riemannSum_sharedAccuracyClose_at : ∀ (x y1 y2 : CReal) (bound1
/// bound2 : Nat → Rat) (l : Nat), (∀ i, Within (sample (x − y1) i) (bound1
/// i)) → (∀ i, Within (sample (x − y2) i) (bound2 i)) → ∀ oi oj jj1 jj2,
/// Within (sample y1 oi − sample y2 oj) (bnd1(l,jj1,oi,bound1) +
/// bnd2(l,jj2,oj,bound2))`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_shared_accuracy_close_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rat = rat_ty(d);
    let bound_ty = d.arrow(nat, rat);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y1_fv = d.fresh_fvar();
    let y1 = d.kernel().fvar(y1_fv);
    let y2_fv = d.fresh_fvar();
    let y2 = d.kernel().fvar(y2_fv);
    let bound1_fv = d.fresh_fvar();
    let bound1 = d.kernel().fvar(bound1_fv);
    let bound2_fv = d.fresh_fvar();
    let bound2 = d.kernel().fvar(bound2_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);

    let h1_ty = shared_index_hyp_ty(d, p, x, y1, bound1);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = shared_index_hyp_ty(d, p, x, y2, bound2);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let oi_fv = d.fresh_fvar();
    let oi = d.kernel().fvar(oi_fv);
    let oj_fv = d.fresh_fvar();
    let oj = d.kernel().fvar(oj_fv);
    let jj1_fv = d.fresh_fvar();
    let jj1 = d.kernel().fvar(jj1_fv);
    let jj2_fv = d.fresh_fvar();
    let jj2 = d.kernel().fvar(jj2_fv);

    let (final_proof, final_bound) = shared_accuracy_close_at_proof(
        d, p, x, y1, y2, bound1, bound2, l, h1, h2, oi, oj, jj1, jj2,
    );

    let a_val = sample(d, p, y1, oi);
    let c_val = sample(d, p, y2, oj);
    let diff = rsub(d, p.rat, a_val, c_val);
    let concl_ty = within(d, p, diff, final_bound);

    let ty = {
        let after_jj2 = d.pi_fv(jj2_fv, nat, concl_ty);
        let after_jj1 = d.pi_fv(jj1_fv, nat, after_jj2);
        let after_oj = d.pi_fv(oj_fv, nat, after_jj1);
        let after_oi = d.pi_fv(oi_fv, nat, after_oj);
        let after_h2 = d.arrow(h2_ty, after_oi);
        let after_h1 = d.arrow(h1_ty, after_h2);
        let after_l = d.pi_fv(l_fv, nat, after_h1);
        let after_bound2 = d.pi_fv(bound2_fv, bound_ty, after_l);
        let after_bound1 = d.pi_fv(bound1_fv, bound_ty, after_bound2);
        let after_y2 = d.pi_fv(y2_fv, carrier, after_bound1);
        let after_y1 = d.pi_fv(y1_fv, carrier, after_y2);
        d.pi_fv(x_fv, carrier, after_y1)
    };
    let value = {
        let with_jj2 = d.lam_fv(jj2_fv, nat, final_proof);
        let with_jj1 = d.lam_fv(jj1_fv, nat, with_jj2);
        let with_oj = d.lam_fv(oj_fv, nat, with_jj1);
        let with_oi = d.lam_fv(oi_fv, nat, with_oj);
        let with_h2 = d.lam_fv(h2_fv, h2_ty, with_oi);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);
        let with_l = d.lam_fv(l_fv, nat, with_h1);
        let with_bound2 = d.lam_fv(bound2_fv, bound_ty, with_l);
        let with_bound1 = d.lam_fv(bound1_fv, bound_ty, with_bound2);
        let with_y2 = d.lam_fv(y2_fv, carrier, with_bound1);
        let with_y1 = d.lam_fv(y1_fv, carrier, with_y2);
        d.lam_fv(x_fv, carrier, with_y1)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_shared_accuracy_close_at,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod riemann_sum_shared_accuracy_close_at_tests {
    use super::*;

    /// **Reproduces the specialization.** [`declare_riemann_sum_shared_accuracy_close`]
    /// now builds its own proof by calling
    /// [`shared_accuracy_close_at_proof`] -- the SAME construction
    /// [`CRealPrelude::riemann_sum_shared_accuracy_close_at`] exposes with
    /// `l`/`h1`/`h2` genuinely `Π`-bound. This test re-derives `l`, `h1`,
    /// `h2`, `bound1_fn`, `bound2_fn` EXTERNALLY, at genuinely FREE `f`, `a`,
    /// `b`, `e`, `k1`, `k2`, `hab`, `u` (never concrete literals -- the
    /// load-bearing case, since a concrete instantiation could paper over a
    /// wrong `Nat.mul_comm`/reassociation the way [`common_refinement`]'s
    /// own test module documents), then applies BOTH the specialized
    /// theorem and the general `_at` theorem and confirms their conclusion
    /// types render IDENTICALLY. A "generalization" that cannot reproduce
    /// its own specialization is wrong.
    #[test]
    fn shared_accuracy_close_at_reproduces_shared_accuracy_close() {
        crate::on_a_deep_stack(shared_accuracy_close_at_reproduces_shared_accuracy_close_body);
    }

    fn shared_accuracy_close_at_reproduces_shared_accuracy_close_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let k1_fv = d.fresh_fvar();
        let k1 = d.kernel().fvar(k1_fv);
        let k2_fv = d.fresh_fvar();
        let k2 = d.kernel().fvar(k2_fv);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let oi_fv = d.fresh_fvar();
        let oi = d.kernel().fvar(oi_fv);
        let oj_fv = d.fresh_fvar();
        let oj = d.kernel().fvar(oj_fv);
        let jj1_fv = d.fresh_fvar();
        let jj1 = d.kernel().fvar(jj1_fv);
        let jj2_fv = d.fresh_fvar();
        let jj2 = d.kernel().fvar(jj2_fv);

        // Reproduce `declare_riemann_sum_shared_accuracy_close`'s own
        // derivation of `l`, `h1`, `h2`, `bound1_fn`, `bound2_fn` -- see that
        // function's own body for the identical sequence.
        let deep = deep_at(&mut d, p, f, a, b, u, e);
        let m1 = NatOps::add(&mut d, deep, k1);
        let m2 = NatOps::add(&mut d, deep, k2);

        let h1 = d.lemma(p.riemann_sum_cauchy, &[f, a, b, e, m2, k1, hab, u]);
        let h2_raw = d.lemma(p.riemann_sum_cauchy, &[f, a, b, e, m1, k2, hab, u]);
        let (l, l2, l2_eq_l) = common_refinement(&mut d, m1, m2);
        let h2 = {
            let rsum_m2_for_motive = rsum(&mut d, p, f, a, b, m2);
            let neg_rsum_m2_for_motive = cneg(&mut d, p, rsum_m2_for_motive);
            nat_rewrite_prop(&mut d, l2, l, l2_eq_l, h2_raw, &|d, x| {
                let rsum_x = rsum(d, p, f, a, b, x);
                let t = cadd(d, p, rsum_x, neg_rsum_m2_for_motive);
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let seq_t_i = sample(d, p, t, i);
                let bound_i = shared_accuracy_bound(d, p, a, b, e, m2, i);
                let claim = within(d, p, seq_t_i, bound_i);
                d.pi_fv(i_fv, nat, claim)
            })
        };

        let rsum_l = rsum(&mut d, p, f, a, b, l);
        let rsum_m1 = rsum(&mut d, p, f, a, b, m1);
        let rsum_m2 = rsum(&mut d, p, f, a, b, m2);
        let bound1_fn = shared_accuracy_bound_fn(&mut d, p, a, b, e, m1);
        let bound2_fn = shared_accuracy_bound_fn(&mut d, p, a, b, e, m2);

        let specialized = d.lemma(
            p.riemann_sum_shared_accuracy_close,
            &[f, a, b, e, k1, k2, hab, u, oi, oj, jj1, jj2],
        );
        let general = d.lemma(
            p.riemann_sum_shared_accuracy_close_at,
            &[
                rsum_l, rsum_m1, rsum_m2, bound1_fn, bound2_fn, l, h1, h2, oi, oj, jj1, jj2,
            ],
        );

        // `specialized`/`general` mention twelve genuinely FREE fvars
        // (`f, a, b, e, k1, k2, hab, u, oi, oj, jj1, jj2`), none bound by any
        // enclosing `pi_fv`/`lam_fv` -- `Kernel::infer` requires every fvar a
        // term mentions to be bound somewhere reachable from the call, else
        // `UnboundFVar` (this module's own doc comment, kernel fact #1).
        // Close both terms over the SAME twelve binders before inferring,
        // mirroring `common_refinement_type_checks_symbolically_body`'s own
        // "wrap in a throwaway binder" idiom.
        let f_ty = fn_ty(&mut d, p);
        let carrier = creal_ty(&mut d, p);
        let hab_ty = cle(&mut d, p, a, b);
        let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);

        let close = |d: &mut IntDev<'_>, body: ExprId| -> ExprId {
            let w = d.lam_fv(jj2_fv, nat, body);
            let w = d.lam_fv(jj1_fv, nat, w);
            let w = d.lam_fv(oj_fv, nat, w);
            let w = d.lam_fv(oi_fv, nat, w);
            let w = d.lam_fv(u_fv, u_ty, w);
            let w = d.lam_fv(hab_fv, hab_ty, w);
            let w = d.lam_fv(k2_fv, nat, w);
            let w = d.lam_fv(k1_fv, nat, w);
            let w = d.lam_fv(e_fv, nat, w);
            let w = d.lam_fv(b_fv, carrier, w);
            let w = d.lam_fv(a_fv, carrier, w);
            d.lam_fv(f_fv, f_ty, w)
        };
        let specialized_closed = close(&mut d, specialized);
        let general_closed = close(&mut d, general);

        let specialized_ty = d
            .kernel()
            .infer(specialized_closed)
            .expect("riemann_sum_shared_accuracy_close application must type-check");
        let general_ty = d
            .kernel()
            .infer(general_closed)
            .expect("riemann_sum_shared_accuracy_close_at application must type-check");

        assert_eq!(
            d.kernel().render_lean(specialized_ty),
            d.kernel().render_lean(general_ty),
            "riemann_sum_shared_accuracy_close_at at the previously-baked (l, h1, h2) \
             must reproduce riemann_sum_shared_accuracy_close's own conclusion"
        );
    }
}

/// `CReal.riemannSum_sharedAccuracyClose`. See
/// [`CRealPrelude::riemann_sum_shared_accuracy_close`] for the full
/// statement and exactly what this is -- and is not yet -- toward
/// `CReal.integral`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_shared_accuracy_close(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    // m1 := deep(e)+k1, m2 := deep(e)+k2 -- SAME e, so one accuracy covers
    // both.
    let deep = deep_at(d, p, f, a, b, u, e);
    let m1 = NatOps::add(d, deep, k1);
    let m2 = NatOps::add(d, deep, k2);

    // Application 1: e:=e, n_refine:=m2, k:=k1. Internally m = deep+k1 = m1,
    // m_prime = succ_mul_succ(m2, m1) -- EXACTLY `common_refinement`'s `l`.
    let h1 = d.lemma(p.riemann_sum_cauchy, &[f, a, b, e, m2, k1, hab, u]);
    // Application 2: e:=e, n_refine:=m1, k:=k2. Internally m = deep+k2 = m2,
    // m_prime = succ_mul_succ(m1, m2) -- `common_refinement`'s `l2`.
    let h2_raw = d.lemma(p.riemann_sum_cauchy, &[f, a, b, e, m1, k2, hab, u]);

    let (l, l2, l2_eq_l) = common_refinement(d, m1, m2);

    // Rewrite l2 -> l inside h2_raw's own ∀i statement, so both applications
    // below land at the SAME shared refinement `l`.
    let h2 = {
        let rsum_m2_for_motive = rsum(d, p, f, a, b, m2);
        let neg_rsum_m2_for_motive = cneg(d, p, rsum_m2_for_motive);
        nat_rewrite_prop(d, l2, l, l2_eq_l, h2_raw, &|d, x| {
            let rsum_x = rsum(d, p, f, a, b, x);
            let t = cadd(d, p, rsum_x, neg_rsum_m2_for_motive);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let seq_t_i = sample(d, p, t, i);
            let bound_i = shared_accuracy_bound(d, p, a, b, e, m2, i);
            let claim = within(d, p, seq_t_i, bound_i);
            d.pi_fv(i_fv, nat, claim)
        })
    };

    let oi_fv = d.fresh_fvar();
    let oi = d.kernel().fvar(oi_fv);
    let oj_fv = d.fresh_fvar();
    let oj = d.kernel().fvar(oj_fv);
    let jj1_fv = d.fresh_fvar();
    let jj1 = d.kernel().fvar(jj1_fv);
    let jj2_fv = d.fresh_fvar();
    let jj2 = d.kernel().fvar(jj2_fv);

    let rsum_l = rsum(d, p, f, a, b, l);
    let rsum_m1 = rsum(d, p, f, a, b, m1);
    let rsum_m2 = rsum(d, p, f, a, b, m2);

    let bound1_fn = shared_accuracy_bound_fn(d, p, a, b, e, m1);
    let bound2_fn = shared_accuracy_bound_fn(d, p, a, b, e, m2);

    // The wiring from here on (two `shared_index_to_canonical` applications
    // sharing `l` as `x`'s own sample index, combined via `chain_within2`)
    // is fully general in `l`/`h1`/`h2` -- see
    // [`shared_accuracy_close_at_proof`]'s own doc comment for why it is
    // factored out rather than inlined here, and
    // [`CRealPrelude::riemann_sum_shared_accuracy_close_at`] for the
    // kernel-visible theorem exposing that generality directly.
    let (final_proof, final_bound) = shared_accuracy_close_at_proof(
        d, p, rsum_l, rsum_m1, rsum_m2, bound1_fn, bound2_fn, l, h1, h2, oi, oj, jj1, jj2,
    );

    let a_val = sample(d, p, rsum_m1, oi);
    let c_val = sample(d, p, rsum_m2, oj);
    let diff = rsub(d, p.rat, a_val, c_val);
    let concl_ty = within(d, p, diff, final_bound);

    let ty = {
        let after_jj2 = d.pi_fv(jj2_fv, nat, concl_ty);
        let after_jj1 = d.pi_fv(jj1_fv, nat, after_jj2);
        let after_oj = d.pi_fv(oj_fv, nat, after_jj1);
        let after_oi = d.pi_fv(oi_fv, nat, after_oj);
        let after_u = d.pi_fv(u_fv, u_ty, after_oi);
        let after_hab = d.arrow(hab_ty, after_u);
        let over_k2 = d.pi_fv(k2_fv, nat, after_hab);
        let over_k1 = d.pi_fv(k1_fv, nat, over_k2);
        let over_e = d.pi_fv(e_fv, nat, over_k1);
        let over_b = d.pi_fv(b_fv, carrier, over_e);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_jj2 = d.lam_fv(jj2_fv, nat, final_proof);
        let with_jj1 = d.lam_fv(jj1_fv, nat, with_jj2);
        let with_oj = d.lam_fv(oj_fv, nat, with_jj1);
        let with_oi = d.lam_fv(oi_fv, nat, with_oj);
        let with_u = d.lam_fv(u_fv, u_ty, with_oi);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_k2 = d.lam_fv(k2_fv, nat, with_hab);
        let over_k1 = d.lam_fv(k1_fv, nat, over_k2);
        let over_e = d.lam_fv(e_fv, nat, over_k1);
        let over_b = d.lam_fv(b_fv, carrier, over_e);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_shared_accuracy_close,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.riemannSumTotalEpsLe` -- the closed-form magnitude lemma
// `riemannSum_cauchy`'s own doc comment (and
// `riemannSum_shared_accuracy_close`'s) name as the actual remaining gate on
// `CReal.integral`: `riemannSum_cauchy`'s `total_eps` is an opaque CReal
// SAMPLE until this turns it into a genuine `K/(e+1)`-shaped rational,
// independent of `m` and needing no hypothesis on `a`/`b` at all. ----------

/// `mul (ofNat (Nat.succ m)) (mul (embed (natDivSucc 1 e)) (mul width
/// (embed (natDivSucc 1 m))))`, `width := width_of a b` --
/// [`declare_riemann_sum_cauchy`]'s own internal `total_eps`, reconstructed
/// EXTERNALLY term-for-term (same `width_of`/`delta_of`/`embed`/`cmul`
/// recipe, in the same order) so the two are the SAME `ExprId`, not merely
/// defeq -- the same idiom [`deep_at`]/[`shared_accuracy_bound`] already use
/// for the same reason.
fn total_eps_of(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    e: ExprId,
    m: ExprId,
) -> ExprId {
    let delta_m = delta_of(d, p, a, b, m);
    let one_nat = d.num(1);
    let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let eps_embed = embed(d, p, eps_rat);
    let eps_term = cmul(d, p, eps_embed, delta_m);
    let sm = d.succ(m);
    let sm_real = d.const_app(p.of_nat, &[sm]);
    cmul(d, p, sm_real, eps_term)
}

/// `(embed (natDivSucc 1 e), width_of a b, proof)`, `proof : Equiv
/// (total_eps_of a b e m) (mul width (embed (natDivSucc 1 e)))`.
///
/// Piece 1 of [`CRealPrelude::riemann_sum_total_eps_le`]:
/// `total_eps_of`'s `(succ m)`-scaled mesh fraction cancels EXACTLY like
/// [`declare_riemann_sum_const`]'s own mesh count does, regardless of what
/// the "constant" factor multiplying the mesh IS -- here `embed (natDivSucc
/// 1 e)` rather than an arbitrary `c`. [`riemann_sum_const_rearrange`]
/// already proves exactly this cancellation generically (its own internal
/// `a_start` is, term-for-term, `total_eps_of`'s construction: `delta := mul
/// width frac_m` matches [`delta_of`]; `w := mul c delta` matches
/// `total_eps_of`'s `eps_term` at `c := eps_embed`; `mul (ofNat (succ m)) w`
/// matches `total_eps_of`'s outer product) -- this reuses it verbatim and
/// only needs one further `mul_comm` to match the width-first order this
/// module's doc comments state.
fn total_eps_equiv_width_eps(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    e: ExprId,
    m: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let width = width_of(d, p, a, b);
    let one_nat = d.num(1);
    let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let eps_embed = embed(d, p, eps_rat);
    let frac_m = {
        let one_nat2 = d.num(1);
        let rat_frac = d.const_app(p.rat.nat_div_succ, &[one_nat2, m]);
        embed(d, p, rat_frac)
    };

    // step_a : Equiv total_eps (mul eps_embed width).
    let step_a = riemann_sum_const_rearrange(d, p, eps_embed, width, frac_m, m);

    let mul_eps_width = cmul(d, p, eps_embed, width);
    let mul_width_eps = cmul(d, p, width, eps_embed);
    let step_b = d.lemma(p.mul_comm, &[eps_embed, width]);

    let total_eps = total_eps_of(d, p, a, b, e, m);
    let proof = d.lemma(
        p.equiv_trans,
        &[total_eps, mul_eps_width, mul_width_eps, step_a, step_b],
    );
    (eps_embed, width, proof)
}

/// `Equiv (mul (ofNat magnitude) (embed (natDivSucc 1 e))) (embed
/// (natDivSucc magnitude e))` -- for ANY `magnitude`, `e`. The first two
/// steps of [`magnitude_times_frac_eq_outer`] (`Rat.natDivSucc_mul` then
/// `Nat.mul_one`) with nothing left to rescale: unlike that lemma, this one
/// carries no Archimedean threshold (`e` need not relate to `magnitude` at
/// all), so its own final `Rat.natDivSucc_scale` step is not needed here.
fn magnitude_times_eps_eq(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    magnitude: ExprId,
    e: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = rat.int.nat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);

    let mag_rat = d.const_app(rat.nat_div_succ, &[magnitude, zero_nat]);
    let eps_rat = d.const_app(rat.nat_div_succ, &[one_nat, e]);
    let mag_real = embed(d, p, mag_rat);
    let eps_real = embed(d, p, eps_rat);
    let product_real = cmul(d, p, mag_real, eps_real);

    let product_rat = rmul(d, mag_rat, eps_rat);
    let fused = {
        let scaled = NatOps::mul(d, magnitude, one_nat);
        d.const_app(rat.nat_div_succ, &[scaled, e])
    };
    let fuse = d.lemma(rat.nat_div_succ_mul, &[magnitude, one_nat, e]);
    let collapsed = d.const_app(rat.nat_div_succ, &[magnitude, e]);
    let collapse = {
        let scaled = NatOps::mul(d, magnitude, one_nat);
        let identity = d.lemma(nat.mul_one, &[magnitude]);
        nat_eq_to_rat(d, scaled, magnitude, identity, &|d, t| {
            d.const_app(rat.nat_div_succ, &[t, e])
        })
    };

    let (_, chain) = rchain(d, product_rat, &[(fused, fuse), (collapsed, collapse)]);

    let of_rat_mul_step = d.lemma(p.of_rat_mul, &[mag_rat, eps_rat]);
    rat_eq_rewrite(
        d,
        product_rat,
        collapsed,
        chain,
        of_rat_mul_step,
        &|d, t| {
            let embedded = embed(d, p, t);
            equiv(d, p, product_real, embedded)
        },
    )
}

/// `le (mul width (embed (natDivSucc 1 e))) (embed (natDivSucc magnitude
/// e))`, given `width_le_mag : le width (ofNat magnitude)`. Mirrors
/// [`step_le_outer_bound`]'s exact shape (nonneg factor on the multiplied
/// side, two `mul_comm` flips, one closing rational identity) with
/// [`magnitude_times_eps_eq`] in place of [`magnitude_times_frac_eq_outer`]
/// -- and, unlike that theorem, no `le a b` hypothesis anywhere: `direct_bound_le`
/// is unconditional and the nonnegative factor here is the RATIONAL `embed
/// (natDivSucc 1 e)`, never `width` itself.
fn width_eps_le_magnitude_eps(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    width: ExprId,
    width_le_mag: ExprId,
    magnitude: ExprId,
    e: ExprId,
) -> ExprId {
    let one_nat = d.num(1);
    let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let eps_embed = embed(d, p, eps_rat);
    let eps_nonneg = {
        let rzero_expr = rzero(d, p.rat);
        let rle_p = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, e]);
        d.lemma(p.of_rat_le, &[rzero_expr, eps_rat, rle_p])
    };

    let step = cmul(d, p, width, eps_embed);
    let eps_width = cmul(d, p, eps_embed, width);
    let comm1 = d.lemma(p.mul_comm, &[width, eps_embed]);

    let om = d.const_app(p.of_nat, &[magnitude]);
    let eps_mag = cmul(d, p, eps_embed, om);
    let scaled = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[eps_embed, width, om, eps_nonneg, width_le_mag],
    );

    let refl_eps_mag = d.lemma(p.equiv_refl, &[eps_mag]);
    let comm1_symm = d.lemma(p.equiv_symm, &[step, eps_width, comm1]);
    let step_le_eps_mag = d.lemma(
        p.le_congr,
        &[
            eps_width,
            step,
            eps_mag,
            eps_mag,
            comm1_symm,
            refl_eps_mag,
            scaled,
        ],
    );

    let mag_eps = cmul(d, p, om, eps_embed);
    let comm2 = d.lemma(p.mul_comm, &[eps_embed, om]);
    let collapse = magnitude_times_eps_eq(d, p, magnitude, e);
    let bound_rat = d.const_app(p.rat.nat_div_succ, &[magnitude, e]);
    let out_bound = embed(d, p, bound_rat);
    let eps_mag_eq_out = d.lemma(
        p.equiv_trans,
        &[eps_mag, mag_eps, out_bound, comm2, collapse],
    );

    let refl_step = d.lemma(p.equiv_refl, &[step]);
    d.lemma(
        p.le_congr,
        &[
            step,
            step,
            eps_mag,
            out_bound,
            refl_step,
            eps_mag_eq_out,
            step_le_eps_mag,
        ],
    )
}

/// `CReal.riemannSumTotalEpsLe`. See
/// [`CRealPrelude::riemann_sum_total_eps_le`] for the full statement and the
/// two-piece route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_total_eps_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let total_eps = total_eps_of(d, p, a, b, e, m);
    let (eps_embed, width, magnitude_equiv) = total_eps_equiv_width_eps(d, p, a, b, e, m);
    let mul_width_eps = cmul(d, p, width, eps_embed);

    let (_c, magnitude, width_le) = direct_bound_le(d, p, width);
    let step_bound = width_eps_le_magnitude_eps(d, p, width, width_le, magnitude, e);

    let bound_rat = d.const_app(p.rat.nat_div_succ, &[magnitude, e]);
    let final_bound = embed(d, p, bound_rat);

    let hx = d.lemma(p.equiv_symm, &[total_eps, mul_width_eps, magnitude_equiv]);
    let hy = d.lemma(p.equiv_refl, &[final_bound]);
    let final_le = d.lemma(
        p.le_congr,
        &[
            mul_width_eps,
            total_eps,
            final_bound,
            final_bound,
            hx,
            hy,
            step_bound,
        ],
    );

    let ty = {
        let concl = cle(d, p, total_eps, final_bound);
        let over_m = d.pi_fv(m_fv, nat, concl);
        let over_e = d.pi_fv(e_fv, nat, over_m);
        let over_b = d.pi_fv(b_fv, carrier, over_e);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, final_le);
        let over_e = d.lam_fv(e_fv, nat, over_m);
        let over_b = d.lam_fv(b_fv, carrier, over_e);
        d.lam_fv(a_fv, carrier, over_b)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_total_eps_le,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.riemannSumDeepCauchy` -- Spivak ch.13->14's Cauchy-shape
// statement for the RAW-indexed sequence `fun n => riemannSum F a b (deep
// n)`, at two INDEPENDENT accuracies `p`, `q` (not one shared `e`, unlike
// [`declare_riemann_sum_shared_accuracy_close`]). This is the reindexing
// route [`declare_shared_index_to_canonical`]'s own doc comment names: `e :=
// n` directly, no inversion of `deep` needed. --------------------------------

/// `CReal.riemannSumDeepCauchy : ∀ F a b, CReal.le a b → CReal.UniformlyContinuousOn
/// F a b → ∀ p q : Nat, Within (Rat.sub (seq (riemannSum F a b (deep F a b u p)) p)
/// (seq (riemannSum F a b (deep F a b u q)) q)) (bound p q)`, `deep` computed
/// EXACTLY the way [`declare_riemann_sum_cauchy`]'s own body computes it (see
/// [`deep_at`]), with the extra depth `k` fixed at `0` (so the sequence is
/// literally `riemannSum F a b (deep p)`, no free `k` left over) and `bound
/// p q := (modulus p (shift p) + shared_accuracy_bound(a,b,p,m1,p)) +
/// modulus (shift p) p) + modulus p q + ((modulus q (shift q) +
/// shared_accuracy_bound(a,b,q,m2,q)) + modulus (shift q) q)`.
///
/// # The construction
///
/// Two [`CRealPrelude::riemann_sum_cauchy`] calls at the two INDEPENDENT
/// accuracies (`e := p`, `n_refine := m2`, `k := 0` for the first; `e := q`,
/// `n_refine := m1`, `k := 0` for the second — `m1 := deep(p)`, `m2 :=
/// deep(q)`), [`common_refinement`] to identify their two refinement targets
/// into a single `l`, then TWO [`CRealPrelude::shared_index_to_canonical`]
/// applications — **the key move, and the one
/// [`declare_shared_index_to_canonical`]'s own doc comment flags as the
/// disproved worry**: rather than leaving `pp`/`qq`/`jj` free (the way
/// [`declare_riemann_sum_shared_accuracy_close`] does, landing `X := rsum_l`
/// at canonical index `l` itself in both applications), THIS construction
/// sets `pp := qq := jj := p` in the first application (`X := rsum_l`, `Y :=
/// rsum_m1`) and `pp := qq := jj := q` in the second (`X := rsum_l`, `Y :=
/// rsum_m2`). Because `sharedIndexToCanonical`'s three index arguments are
/// genuinely free `Nat`s, unconstrained by `l`'s own magnitude, this choice
/// is available, and it is what makes EVERY leg of the resulting bound a
/// function of `p`/`q` alone: `modulus(p, shift p)` and `modulus(shift p,
/// p)` are `rsum_l`'s own regularity at indices built from `p` alone (not
/// `l`), and the hypothesis leg reads `H(p)`, i.e. `riemann_sum_cauchy`'s
/// OWN bound at exactly the sample index the final statement is stated at.
///
/// This leaves `rsum_l` sampled at TWO DIFFERENT indices — `l`'s stand-in
/// `p` from the first application, `q` from the second — so a third,
/// genuinely new leg bridges them: `rsum_l`'s own [`CRealPrelude::regular`]
/// between `p` and `q` directly (no dependence on `l`'s internal
/// construction at all, since `regular` is a property every `CReal`
/// satisfies uniformly). [`chain_within3`] fuses the three legs — `seq
/// rsum_m1 p → seq rsum_l p` (the first application, flipped via
/// [`within_symm`]), `seq rsum_l p → seq rsum_l q` (the bridging `regular`
/// leg), `seq rsum_l q → seq rsum_m2 q` (the second application) — into the
/// single three-leg `Within` this declaration states.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_deep_cauchy(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let pn_fv = d.fresh_fvar();
    let pn = d.kernel().fvar(pn_fv);
    let qn_fv = d.fresh_fvar();
    let qn = d.kernel().fvar(qn_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    // m1 := deep(f,a,b,u,pn) + 0, m2 := deep(f,a,b,u,qn) + 0 -- built with
    // the SAME `+0` shape `riemann_sum_cauchy`'s own internal `m := deep +
    // k` computes at `k := 0`, so the terms below are the SAME ExprId as
    // what `h1`/`h2_raw`'s own conclusion types mention -- no bridging
    // lemma needed, the same idiom `deep_at`'s own doc comment names.
    let deep1 = deep_at(d, p, f, a, b, u, pn);
    let deep2 = deep_at(d, p, f, a, b, u, qn);
    let zero1 = d.num(0);
    let m1 = NatOps::add(d, deep1, zero1);
    let zero2 = d.num(0);
    let m2 = NatOps::add(d, deep2, zero2);

    // Application 1: e := pn, n_refine := m2, k := zero1. Internal m = m1,
    // m_prime = succ_mul_succ(m2, m1) == common_refinement's `l`.
    let h1 = d.lemma(p.riemann_sum_cauchy, &[f, a, b, pn, m2, zero1, hab, u]);
    // Application 2: e := qn, n_refine := m1, k := zero2. Internal m = m2,
    // m_prime = succ_mul_succ(m1, m2) == common_refinement's `l2`.
    let h2_raw = d.lemma(p.riemann_sum_cauchy, &[f, a, b, qn, m1, zero2, hab, u]);

    let (l, l2, l2_eq_l) = common_refinement(d, m1, m2);

    // Rewrite l2 -> l inside h2_raw's own ∀i statement, so both applications
    // below land at the SAME shared refinement `l` -- verbatim shape of
    // `declare_riemann_sum_shared_accuracy_close`'s own `h2`, with `e :=
    // qn`.
    let h2 = {
        let rsum_m2_for_motive = rsum(d, p, f, a, b, m2);
        let neg_rsum_m2_for_motive = cneg(d, p, rsum_m2_for_motive);
        nat_rewrite_prop(d, l2, l, l2_eq_l, h2_raw, &|d, x| {
            let rsum_x = rsum(d, p, f, a, b, x);
            let t = cadd(d, p, rsum_x, neg_rsum_m2_for_motive);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let seq_t_i = sample(d, p, t, i);
            let bound_i = shared_accuracy_bound(d, p, a, b, qn, m2, i);
            let claim = within(d, p, seq_t_i, bound_i);
            d.pi_fv(i_fv, nat, claim)
        })
    };

    let rsum_l = rsum(d, p, f, a, b, l);
    let rsum_m1 = rsum(d, p, f, a, b, m1);
    let rsum_m2 = rsum(d, p, f, a, b, m2);

    let bound1_fn = shared_accuracy_bound_fn(d, p, a, b, pn, m1);
    let bound2_fn = shared_accuracy_bound_fn(d, p, a, b, qn, m2);

    // app1 : Within (seq rsum_l pn - seq rsum_m1 pn) bnd_a -- `pp := qq :=
    // jj := pn`, the disproved-worry specialization.
    let app1 = d.lemma(
        p.shared_index_to_canonical,
        &[rsum_l, rsum_m1, bound1_fn, h1, pn, pn, pn],
    );
    // app2 : Within (seq rsum_l qn - seq rsum_m2 qn) bnd_c -- `pp := qq :=
    // jj := qn`.
    let app2 = d.lemma(
        p.shared_index_to_canonical,
        &[rsum_l, rsum_m2, bound2_fn, h2, qn, qn, qn],
    );

    let x_val = sample(d, p, rsum_m1, pn);
    let y_val = sample(d, p, rsum_l, pn);
    let z_val = sample(d, p, rsum_l, qn);
    let w_val = sample(d, p, rsum_m2, qn);

    let shift_pn = shift(d, pn);
    let m_pn_spn = modulus(d, p, pn, shift_pn);
    let bound1_pn = d.apply(bound1_fn, &[pn]);
    let m_spn_pn = modulus(d, p, shift_pn, pn);
    let bnd_a_inner = radd(d, m_pn_spn, bound1_pn);
    let bnd_a = radd(d, bnd_a_inner, m_spn_pn);

    let bnd_b = modulus(d, p, pn, qn);

    let shift_qn = shift(d, qn);
    let m_qn_sqn = modulus(d, p, qn, shift_qn);
    let bound2_qn = d.apply(bound2_fn, &[qn]);
    let m_sqn_qn = modulus(d, p, shift_qn, qn);
    let bnd_c_inner = radd(d, m_qn_sqn, bound2_qn);
    let bnd_c = radd(d, bnd_c_inner, m_sqn_qn);

    // leg_a : Within (x_val - y_val) bnd_a, flipped from app1 : Within
    // (y_val - x_val) bnd_a.
    let leg_a = within_symm(d, p, y_val, x_val, bnd_a, app1);
    // leg_b : Within (y_val - z_val) bnd_b -- `rsum_l`'s OWN regularity
    // between `pn` and `qn`, independent of `l`'s internal construction.
    let leg_b = d.lemma(p.regular, &[rsum_l, pn, qn]);
    // leg_c : Within (z_val - w_val) bnd_c, directly from app2.
    let leg_c = app2;

    let proof = chain_within3(
        d, p, x_val, y_val, z_val, w_val, bnd_a, bnd_b, bnd_c, leg_a, leg_b, leg_c,
    );

    // `chain_within3`'s own bound shape: (bnd_a+bnd_b)+bnd_c.
    let final_bound = {
        let ab = radd(d, bnd_a, bnd_b);
        radd(d, ab, bnd_c)
    };
    let concl_ty = {
        let diff = rsub(d, p.rat, x_val, w_val);
        within(d, p, diff, final_bound)
    };

    let ty = {
        let after_u = d.pi_fv(u_fv, u_ty, concl_ty);
        let after_hab = d.arrow(hab_ty, after_u);
        let over_qn = d.pi_fv(qn_fv, nat, after_hab);
        let over_pn = d.pi_fv(pn_fv, nat, over_qn);
        let over_b = d.pi_fv(b_fv, carrier, over_pn);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_u = d.lam_fv(u_fv, u_ty, proof);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_qn = d.lam_fv(qn_fv, nat, with_hab);
        let over_pn = d.lam_fv(pn_fv, nat, over_qn);
        let over_b = d.lam_fv(b_fv, carrier, over_pn);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_deep_cauchy,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.riemannSumDeepCauchyFolded` -- folding `riemannSumDeepCauchy`'s
// three-leg `bound(p,q)` into the literal `Cauchy`-rate shape
// `natDivSucc(K,p) + natDivSucc(K,q)`, `K` a `Nat` expression built purely
// from `magnitude := Nat.succ (CReal.bound (width_of a b))` -- independent
// of `p`, `q`, `F`, `u`. This is the last gate before `CReal.integral`:
// `CReal.regular_of_scaled_cauchy` needs EXACTLY this shape. -------------

/// `Rat.natDivSucc k idx`, for a (possibly non-literal) `Nat` expression
/// `k` -- [`div_succ`]'s generalization off a `u32` literal.
fn nds(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, idx: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, idx])
}

/// Fuse `radd(nds(a,idx), nds(b,idx))` into `nds(a+b,idx)` via
/// [`RatPrelude::nat_div_succ_add`](crate::RatPrelude::nat_div_succ_add).
/// Returns `(a+b, Eq Rat (radd(nds(a,idx),nds(b,idx))) (nds(a+b,idx)))`.
fn fuse_nds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    idx: ExprId,
) -> (ExprId, ExprId) {
    let sum = NatOps::add(d, a, b);
    let eq = d.lemma(p.rat.nat_div_succ_add, &[a, b, idx]);
    (sum, eq)
}

/// `Rat.le (sample(totalEps(a,b,e,m), n)) (radd(natDivSucc(magnitude,e),
/// natDivSucc(2,n)))` -- the INDEPENDENT-index generalization of
/// [`total_eps_sample_le`]: `e` (the accuracy `totalEps` and `bound_rat` are
/// BUILT from) and `n` (the raw index the resulting `CReal.le` proof term is
/// APPLIED at) are two free parameters, never assumed equal. This is the
/// generalization this module's own doc comment (the "eleventh lane" entry,
/// just above [`rat_sub_add_cancel`]) names as needed before an
/// `integral_split` assembly can combine three sub-intervals' bounds at
/// independently chosen accuracies -- "mechanical, not new mathematics",
/// since [`CRealPrelude::le`]'s underlying proof term can be `d.apply`'d at
/// ANY raw `Nat` index regardless of which index built the witness (the
/// SAME transparency [`one_sided_two_index`]'s own two-index generalization
/// of `uniform_convergence.rs`'s `one_sided_via_samples` already relies on).
///
/// [`total_eps_sample_le`] is now this function's `n := e` specialization
/// (see that function's own body); `bnd_leg_plus_share_le`, its one existing
/// caller, is unaffected -- it still calls [`total_eps_sample_le`] at a
/// single shared index, unchanged.
#[allow(clippy::too_many_arguments)]
fn total_eps_sample_le_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    e: ExprId,
    m: ExprId,
    magnitude: ExprId,
    n: ExprId,
) -> ExprId {
    let rat = p.rat;
    let total_eps = total_eps_of(d, p, a, b, e, m);
    let bound_rat = nds(d, p, magnitude, e);
    let t = d.lemma(p.riemann_sum_total_eps_le, &[a, b, e, m]);
    let applied = d.apply(t, &[n]);
    let sample_te = sample(d, p, total_eps, n);
    let two_n = div_succ(d, p, 2, n);
    d.lemma(rat.le_of_sub_le, &[sample_te, bound_rat, two_n, applied])
}

/// `Rat.le (sample(totalEps(a,b,idx,m), idx)) (radd(natDivSucc(magnitude,idx),
/// natDivSucc(2,idx)))`.
///
/// Applies [`CRealPrelude::riemann_sum_total_eps_le`] directly to `idx` --
/// relying on [`CRealPrelude::le`]'s `Regular` hint to unfold the resulting
/// `CReal.le` proof term into its `Rat.le` body at that index (mirroring
/// [`direct_bound_le`]'s own converse use of that transparency: building a
/// `le`-typed term FROM a Pi-shaped lambda; this is the same unfolding used
/// in the other direction), and on [`embed`] (`CReal.ofRat`)'s own `seq`
/// reduction (`seq (ofRat q) n` iota/beta-reduces to `q`, since `ofRat q :=
/// CReal.mk (fun _ => q) _`) so the applied term's second (subtracted)
/// sample collapses to the bare rational bound. [`RatPrelude::le_of_sub_le`]
/// then turns the resulting `u − v ≤ q` into `u ≤ v + q`.
///
/// Now [`total_eps_sample_le_at`]'s `n := idx` specialization, kept as a
/// separate named function (rather than inlined at its one call site) so
/// [`bnd_leg_plus_share_le`]'s own doc comment can keep naming it directly.
fn total_eps_sample_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    idx: ExprId,
    m: ExprId,
    magnitude: ExprId,
) -> ExprId {
    total_eps_sample_le_at(d, p, a, b, idx, m, magnitude, idx)
}

#[cfg(test)]
mod total_eps_sample_le_at_tests {
    use super::*;

    /// **Reproduces the specialization, and is not vacuously general.**
    /// [`total_eps_sample_le`] is now defined as [`total_eps_sample_le_at`]'s
    /// `n := idx` case; confirm the two produce the SAME proof term's type
    /// at concrete `a := zero, b := one, idx := m := 6` -- the
    /// discriminating "reproduces the specialization" check this module's
    /// own generalization standard asks for (mirroring `congruence.rs`'s
    /// `rederive_abs_congr_matches_hand_built`).
    ///
    /// The SAME construction at a genuinely DIFFERENT sample index `n := 3
    /// != idx` must NOT render identically -- confirming the generalization
    /// actually depends on `n` (via `sample(total_eps, n)` and
    /// `natDivSucc(2, n)`), rather than silently ignoring it.
    #[test]
    fn total_eps_sample_le_at_reproduces_shared_index_case() {
        crate::on_a_deep_stack(total_eps_sample_le_at_reproduces_shared_index_case_body);
    }

    fn total_eps_sample_le_at_reproduces_shared_index_case_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let a = d.kernel().const_(p.zero, vec![]);
        let b = d.kernel().const_(p.one, vec![]);
        let idx = d.num(6);
        let m = d.num(6);
        let n = d.num(3);

        let width = width_of(&mut d, p, a, b);
        let (_c, magnitude, _width_le) = direct_bound_le(&mut d, p, width);

        let shared = total_eps_sample_le(&mut d, p, a, b, idx, m, magnitude);
        let shared_via_at = total_eps_sample_le_at(&mut d, p, a, b, idx, m, magnitude, idx);
        let independent = total_eps_sample_le_at(&mut d, p, a, b, idx, m, magnitude, n);

        let shared_ty = d
            .kernel()
            .infer(shared)
            .expect("total_eps_sample_le's proof must type-check");
        let shared_via_at_ty = d
            .kernel()
            .infer(shared_via_at)
            .expect("total_eps_sample_le_at at n:=idx must type-check");
        let independent_ty = d
            .kernel()
            .infer(independent)
            .expect("total_eps_sample_le_at at an independent n must type-check");

        assert_eq!(
            d.kernel().render_lean(shared_ty),
            d.kernel().render_lean(shared_via_at_ty),
            "total_eps_sample_le must reproduce total_eps_sample_le_at's n:=idx case"
        );
        assert_ne!(
            d.kernel().render_lean(shared_ty),
            d.kernel().render_lean(independent_ty),
            "total_eps_sample_le_at at an INDEPENDENT n must differ from the shared-index case"
        );
    }
}

/// Folds one side (`idx ∈ {p, q}`) of [`declare_riemann_sum_deep_cauchy`]'s
/// own three-leg bound (`bnd_a`/`bnd_c`), TOGETHER with the matching half of
/// the shared `bnd_b := modulus(p, q)` leg, into a single `natDivSucc(K,
/// idx)`. `K` is built purely from `magnitude` (never from `idx`, `m`, or
/// `bound_at_idx`), so calling this twice -- once at `idx := p`, once at
/// `idx := q`, both with the SAME `magnitude` -- yields the identical `K`
/// `ExprId` by construction (this module's pervasive hash-consing idiom;
/// see [`deep_at`]'s own doc comment for the precedent).
///
/// `bound_at_idx` is the caller's own already-built leaf term (`bound1_pn`/
/// `bound2_qn` in [`declare_riemann_sum_deep_cauchy_folded`], the same
/// `d.apply(bound_fn, &[idx])` shape [`declare_riemann_sum_deep_cauchy`]
/// itself builds). This function's own bound on it is stated against the
/// UNFOLDED `radd(sample_te, natDivSucc(2,idx))` shape instead -- one beta
/// step away, with every other subterm identical by construction -- so the
/// combining step below is accepted up to that one-step defeq rather than
/// needing an explicit bridging lemma, mirroring how
/// `declare_riemann_sum_deep_cauchy` itself already mixes the two forms.
///
/// Returns `(K, proof)`, `proof : Rat.le (radd(bnd_leg, natDivSucc(1,idx)))
/// (natDivSucc(K,idx))`, `bnd_leg := radd(radd(modulus(idx,shift idx),
/// bound_at_idx), modulus(shift idx,idx))` -- EXACTLY
/// [`declare_riemann_sum_deep_cauchy`]'s own `bnd_a`/`bnd_c`, so `proof`'s
/// left side is that declaration's own leaf term, not a reconstruction of
/// it.
///
/// The leaf count: `modulus(idx,shift idx)`'s exact leg is `natDivSucc(1,
/// idx)` outright; its `shift`-side leg is weakened to `natDivSucc(1,idx)`
/// via [`half_shift_le`] (no `Nat.le idx (shift idx)` needed at all --
/// `half_shift_le` reaches the same bound through the halving identity
/// `Rat.natDivSucc_halve` instead of antitonicity); `bound_at_idx` weakens to
/// `natDivSucc(magnitude,idx) + 2×natDivSucc(2,idx)` via
/// [`total_eps_sample_le`]; `modulus(shift idx,idx)` mirrors the first pair.
/// Fusing all of it plus the shared `natDivSucc(1,idx)` extra gives
/// `magnitude + (1+1) + (1+1) + (2+2) + 1 = magnitude + 9` -- matching the
/// roadmap's own `K := CReal.bound(b−a) + 1 + 9` (`magnitude = CReal.bound
/// (width) + 1` by [`direct_bound_le`]) -- though `K` is returned as
/// whatever `Nat` expression this fold naturally produces (a deterministic
/// function of `magnitude` alone), not re-normalized into that literal
/// shape.
fn bnd_leg_plus_share_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    idx: ExprId,
    m: ExprId,
    magnitude: ExprId,
    bound_at_idx: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    let a1 = div_succ(d, p, 1, idx);
    let shift_idx = shift(d, idx);
    let a2 = div_succ(d, p, 1, shift_idx);
    let b1 = div_succ(d, p, 2, idx);
    let m_term = nds(d, p, magnitude, idx);

    // --- order half: bnd_leg(idx,m) + natDivSucc(1,idx) ≤ R. --------------
    let a2_le_a1 = half_shift_le(d, p, idx);
    let refl_a1 = d.lemma(rat.le_refl, &[a1]);

    let modulus_idx_shift = modulus(d, p, idx, shift_idx); // = radd(a1,a2)
    let modulus_shift_idx = modulus(d, p, shift_idx, idx); // = radd(a2,a1)

    // modulus(idx, shift idx) ≤ a1 + a1.
    let mod1_le = d.lemma(rat.add_le_add, &[a1, a1, a2, a1, refl_a1, a2_le_a1]);
    // modulus(shift idx, idx) ≤ a1 + a1.
    let mod2_le = d.lemma(rat.add_le_add, &[a2, a1, a1, a1, a2_le_a1, refl_a1]);

    // bound_at_idx ≤ (m_term + b1) + b1  [up to the one-beta defeq noted above].
    let sample_le = total_eps_sample_le(d, p, a, b, idx, m, magnitude);
    let refl_b1 = d.lemma(rat.le_refl, &[b1]);
    let total_eps = total_eps_of(d, p, a, b, idx, m);
    let sample_te = sample(d, p, total_eps, idx);
    let m_plus_b1 = radd(d, m_term, b1);
    let bound_le = d.lemma(
        rat.add_le_add,
        &[sample_te, m_plus_b1, b1, b1, sample_le, refl_b1],
    );

    let a1a1 = radd(d, a1, a1);
    let inner_target = radd(d, m_plus_b1, b1);
    let part1_actual = radd(d, modulus_idx_shift, bound_at_idx);
    let part1_target = radd(d, a1a1, inner_target);
    let part1_le = d.lemma(
        rat.add_le_add,
        &[
            modulus_idx_shift,
            a1a1,
            bound_at_idx,
            inner_target,
            mod1_le,
            bound_le,
        ],
    );

    let bnd_leg_actual = radd(d, part1_actual, modulus_shift_idx);
    let bnd_leg_target = radd(d, part1_target, a1a1);
    let bnd_leg_le = d.lemma(
        rat.add_le_add,
        &[
            part1_actual,
            part1_target,
            modulus_shift_idx,
            a1a1,
            part1_le,
            mod2_le,
        ],
    );

    let with_extra_target = radd(d, bnd_leg_target, a1);
    let with_extra_le = d.lemma(
        rat.add_le_add,
        &[bnd_leg_actual, bnd_leg_target, a1, a1, bnd_leg_le, refl_a1],
    );

    // --- equality half: fold `with_extra_target` into one `natDivSucc`. ---
    let (n1, eq_a) = fuse_nds(d, p, magnitude, two_nat, idx); // m_term+b1 = nds(n1,idx)
    let n1_idx = nds(d, p, n1, idx);
    let (n2, eq_b) = fuse_nds(d, p, n1, two_nat, idx); // nds(n1,idx)+b1 = nds(n2,idx)
    let n2_idx = nds(d, p, n2, idx);
    let eq_inner_left = rcongr(d, m_plus_b1, n1_idx, eq_a, &|d, t| radd(d, t, b1));
    let n1_idx_plus_b1 = radd(d, n1_idx, b1);
    let eq_inner = rtrans(d, inner_target, n1_idx_plus_b1, n2_idx, eq_inner_left, eq_b);

    let (n3, eq_c) = fuse_nds(d, p, one_nat, one_nat, idx); // a1+a1 = nds(n3,idx)
    let n3_idx = nds(d, p, n3, idx);

    let eq_part1_left = rcongr(d, a1a1, n3_idx, eq_c, &|d, t| radd(d, t, inner_target));
    let eq_part1_right = rcongr(d, inner_target, n2_idx, eq_inner, &|d, t| {
        radd(d, n3_idx, t)
    });
    let n3_idx_plus_inner = radd(d, n3_idx, inner_target);
    let n3_idx_plus_n2_idx = radd(d, n3_idx, n2_idx);
    let eq_part1 = rtrans(
        d,
        part1_target,
        n3_idx_plus_inner,
        n3_idx_plus_n2_idx,
        eq_part1_left,
        eq_part1_right,
    );
    let (n4, eq_d) = fuse_nds(d, p, n3, n2, idx);
    let n4_idx = nds(d, p, n4, idx);
    let eq_part1_full = rtrans(d, part1_target, n3_idx_plus_n2_idx, n4_idx, eq_part1, eq_d);

    let eq_bnd_leg_left = rcongr(d, part1_target, n4_idx, eq_part1_full, &|d, t| {
        radd(d, t, a1a1)
    });
    let eq_bnd_leg_right = rcongr(d, a1a1, n3_idx, eq_c, &|d, t| radd(d, n4_idx, t));
    let n4_idx_plus_a1a1 = radd(d, n4_idx, a1a1);
    let n4_idx_plus_n3_idx = radd(d, n4_idx, n3_idx);
    let eq_bnd_leg = rtrans(
        d,
        bnd_leg_target,
        n4_idx_plus_a1a1,
        n4_idx_plus_n3_idx,
        eq_bnd_leg_left,
        eq_bnd_leg_right,
    );
    let (n5, eq_e) = fuse_nds(d, p, n4, n3, idx);
    let n5_idx = nds(d, p, n5, idx);
    let eq_bnd_leg_full = rtrans(
        d,
        bnd_leg_target,
        n4_idx_plus_n3_idx,
        n5_idx,
        eq_bnd_leg,
        eq_e,
    );

    let eq_with_extra_left = rcongr(d, bnd_leg_target, n5_idx, eq_bnd_leg_full, &|d, t| {
        radd(d, t, a1)
    });
    let (k, eq_f) = fuse_nds(d, p, n5, one_nat, idx);
    let k_idx = nds(d, p, k, idx);
    let n5_idx_plus_a1 = radd(d, n5_idx, a1);
    let eq_with_extra = rtrans(
        d,
        with_extra_target,
        n5_idx_plus_a1,
        k_idx,
        eq_with_extra_left,
        eq_f,
    );

    let with_extra_actual = radd(d, bnd_leg_actual, a1);
    let final_le = rat_eq_rewrite(
        d,
        with_extra_target,
        k_idx,
        eq_with_extra,
        with_extra_le,
        &|d, t| rle(d, rat, with_extra_actual, t),
    );

    (k, final_le)
}

/// The `[a,c]`-leg generalization of [`bnd_leg_plus_share_le`]: identical
/// structure (same `a1`/`a2`/`shift`/`b1` bookkeeping, same
/// `half_shift_le`-weakened `modulus` pair, same fold into a single
/// `natDivSucc`), but the `bound_at_idx` weakening step consumes
/// [`total_eps_sample_le_at`] at an INDEPENDENT accuracy `e` and sample
/// index `jj1` — `bnd_leg_plus_share_le`'s own `total_eps_sample_le` call is
/// that function's `n := idx` specialization, so `e := jj1` recovers it
/// exactly.
///
/// Because `m_term := nds(magnitude, e)` and every other leaf
/// (`a1`/`a2`/`b1`) is built at `jj1`, [`fuse_nds`] cannot fold `m_term`
/// together with them (it fuses two `natDivSucc`s at the SAME index only).
/// So `m_term` is pulled out to the front of the sum instead of into it: one
/// `Rat.add_assoc` isolates `b1+b1` inside `inner_target`, one
/// [`reassoc3`] application (`Eq (a1a1 + (m_term + b1b1)) (m_term + (b1b1 +
/// a1a1))`) moves `m_term` past the first `a1a1`, and every step after that
/// stays in the shape `radd(m_term, natDivSucc(_, jj1))` by construction, so
/// only plain `Rat.add_assoc` (never another commute) is needed to keep
/// folding the `jj1`-side terms as [`bnd_leg_plus_share_le`] itself does.
///
/// Returns `(k, proof)`, `proof : Rat.le (radd(bnd_leg_actual, natDivSucc(1,
/// jj1))) (radd(m_term, natDivSucc(k, jj1)))` — `bnd_leg_actual` is
/// EXACTLY [`bnd_leg_plus_share_le`]'s own leaf shape (`modulus(jj1,shift
/// jj1) + bound_at_idx) + modulus(shift jj1,jj1)`, at `jj1` throughout, so a
/// caller substitutes this directly wherever `bnd_leg_plus_share_le`'s own
/// result is substituted today. `k` is independent of `magnitude` and of
/// `e` — a concrete instantiation confirms it is defeq to the literal `9`,
/// matching [`bnd_leg_plus_share_le`]'s own doc-commented leaf count
/// (`magnitude + 9`) with the `magnitude` term now carried separately in
/// `m_term` instead of folded in.
#[allow(clippy::too_many_arguments)]
fn bnd_leg_plus_share_le_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    e: ExprId,
    jj1: ExprId,
    m: ExprId,
    magnitude: ExprId,
    bound_at_idx: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    let a1 = div_succ(d, p, 1, jj1);
    let shift_jj1 = shift(d, jj1);
    let a2 = div_succ(d, p, 1, shift_jj1);
    let b1 = div_succ(d, p, 2, jj1);
    let m_term = nds(d, p, magnitude, e);

    // --- order half: bnd_leg(jj1,m) + natDivSucc(1,jj1) ≤ R. --------------
    let a2_le_a1 = half_shift_le(d, p, jj1);
    let refl_a1 = d.lemma(rat.le_refl, &[a1]);

    let modulus_idx_shift = modulus(d, p, jj1, shift_jj1); // = radd(a1,a2)
    let modulus_shift_idx = modulus(d, p, shift_jj1, jj1); // = radd(a2,a1)

    let mod1_le = d.lemma(rat.add_le_add, &[a1, a1, a2, a1, refl_a1, a2_le_a1]);
    let mod2_le = d.lemma(rat.add_le_add, &[a2, a1, a1, a1, a2_le_a1, refl_a1]);

    // bound_at_idx ≤ (m_term + b1) + b1 [up to the one-beta defeq noted on
    // `bnd_leg_plus_share_le`], via the independent-index generalization.
    let sample_le = total_eps_sample_le_at(d, p, a, b, e, m, magnitude, jj1);
    let refl_b1 = d.lemma(rat.le_refl, &[b1]);
    let total_eps = total_eps_of(d, p, a, b, e, m);
    let sample_te = sample(d, p, total_eps, jj1);
    let m_plus_b1 = radd(d, m_term, b1);
    let bound_le = d.lemma(
        rat.add_le_add,
        &[sample_te, m_plus_b1, b1, b1, sample_le, refl_b1],
    );

    let a1a1 = radd(d, a1, a1);
    let inner_target = radd(d, m_plus_b1, b1);
    let part1_actual = radd(d, modulus_idx_shift, bound_at_idx);
    let part1_target = radd(d, a1a1, inner_target);
    let part1_le = d.lemma(
        rat.add_le_add,
        &[
            modulus_idx_shift,
            a1a1,
            bound_at_idx,
            inner_target,
            mod1_le,
            bound_le,
        ],
    );

    let bnd_leg_actual = radd(d, part1_actual, modulus_shift_idx);
    let bnd_leg_target = radd(d, part1_target, a1a1);
    let bnd_leg_le = d.lemma(
        rat.add_le_add,
        &[
            part1_actual,
            part1_target,
            modulus_shift_idx,
            a1a1,
            part1_le,
            mod2_le,
        ],
    );

    let with_extra_target = radd(d, bnd_leg_target, a1);
    let with_extra_le = d.lemma(
        rat.add_le_add,
        &[bnd_leg_actual, bnd_leg_target, a1, a1, bnd_leg_le, refl_a1],
    );

    // --- equality half: pull `m_term` to the front, fold the rest at `jj1`.
    // inner_target = (m_term+b1)+b1 ≡ m_term+(b1+b1) ≡ m_term+natDivSucc(nb4,jj1).
    let assoc_inner = d.lemma(rat.add_assoc, &[m_term, b1, b1]);
    let b1_b1 = radd(d, b1, b1);
    let m_term_plus_b1b1 = radd(d, m_term, b1_b1);
    let (nb4, eq_b1b1) = fuse_nds(d, p, two_nat, two_nat, jj1);
    let nb4_idx = nds(d, p, nb4, jj1);
    let eq_inner_right = rcongr(d, b1_b1, nb4_idx, eq_b1b1, &|d, t| radd(d, m_term, t));
    let m_term_plus_nb4 = radd(d, m_term, nb4_idx);
    let eq_inner = rtrans(
        d,
        inner_target,
        m_term_plus_b1b1,
        m_term_plus_nb4,
        assoc_inner,
        eq_inner_right,
    );

    // a1a1 = natDivSucc(n3,jj1).
    let (n3, eq_c) = fuse_nds(d, p, one_nat, one_nat, jj1);
    let n3_idx = nds(d, p, n3, jj1);

    // part1_target = a1a1 + inner_target ≡ n3_idx + (m_term + nb4_idx)
    //              ≡ [reassoc3] m_term + (nb4_idx + n3_idx)
    //              ≡ m_term + natDivSucc(n4,jj1).
    let eq_part1_left = rcongr(d, a1a1, n3_idx, eq_c, &|d, t| radd(d, t, inner_target));
    let n3_idx_plus_inner = radd(d, n3_idx, inner_target);
    let eq_part1_right = rcongr(d, inner_target, m_term_plus_nb4, eq_inner, &|d, t| {
        radd(d, n3_idx, t)
    });
    let n3_idx_plus_mnb4 = radd(d, n3_idx, m_term_plus_nb4);
    let eq_part1_pre = rtrans(
        d,
        part1_target,
        n3_idx_plus_inner,
        n3_idx_plus_mnb4,
        eq_part1_left,
        eq_part1_right,
    );
    let (reassoc1_target, reassoc1_proof) = reassoc3(d, p, n3_idx, m_term, nb4_idx);
    let eq_part1_full = rtrans(
        d,
        part1_target,
        n3_idx_plus_mnb4,
        reassoc1_target,
        eq_part1_pre,
        reassoc1_proof,
    );
    let (n4, eq_d) = fuse_nds(d, p, nb4, n3, jj1);
    let n4_idx = nds(d, p, n4, jj1);
    let nb4_plus_n3 = radd(d, nb4_idx, n3_idx);
    let eq_part1_inner = rcongr(d, nb4_plus_n3, n4_idx, eq_d, &|d, t| radd(d, m_term, t));
    let m_term_plus_n4 = radd(d, m_term, n4_idx);
    let eq_part1_final = rtrans(
        d,
        part1_target,
        reassoc1_target,
        m_term_plus_n4,
        eq_part1_full,
        eq_part1_inner,
    );

    // bnd_leg_target = part1_target + a1a1 ≡ (m_term+n4_idx) + n3_idx
    //                ≡ [add_assoc] m_term + (n4_idx+n3_idx)
    //                ≡ m_term + natDivSucc(n5,jj1).
    let eq_bnd_step1 = rcongr(d, part1_target, m_term_plus_n4, eq_part1_final, &|d, t| {
        radd(d, t, a1a1)
    });
    let m_term_n4_plus_a1a1 = radd(d, m_term_plus_n4, a1a1);
    let eq_bnd_step2 = rcongr(d, a1a1, n3_idx, eq_c, &|d, t| radd(d, m_term_plus_n4, t));
    let m_term_n4_plus_n3 = radd(d, m_term_plus_n4, n3_idx);
    let eq_bnd_pre = rtrans(
        d,
        bnd_leg_target,
        m_term_n4_plus_a1a1,
        m_term_n4_plus_n3,
        eq_bnd_step1,
        eq_bnd_step2,
    );
    let assoc_bnd = d.lemma(rat.add_assoc, &[m_term, n4_idx, n3_idx]);
    let n4_plus_n3 = radd(d, n4_idx, n3_idx);
    let m_term_plus_n4n3 = radd(d, m_term, n4_plus_n3);
    let eq_bnd_full = rtrans(
        d,
        bnd_leg_target,
        m_term_n4_plus_n3,
        m_term_plus_n4n3,
        eq_bnd_pre,
        assoc_bnd,
    );
    let (n5, eq_e) = fuse_nds(d, p, n4, n3, jj1);
    let n5_idx = nds(d, p, n5, jj1);
    let eq_bnd_inner = rcongr(d, n4_plus_n3, n5_idx, eq_e, &|d, t| radd(d, m_term, t));
    let m_term_plus_n5 = radd(d, m_term, n5_idx);
    let eq_bnd_final = rtrans(
        d,
        bnd_leg_target,
        m_term_plus_n4n3,
        m_term_plus_n5,
        eq_bnd_full,
        eq_bnd_inner,
    );

    // with_extra_target = bnd_leg_target + a1 ≡ (m_term+n5_idx) + a1
    //                   ≡ [add_assoc] m_term + (n5_idx+a1)
    //                   ≡ m_term + natDivSucc(k,jj1).
    let eq_we_pre = rcongr(d, bnd_leg_target, m_term_plus_n5, eq_bnd_final, &|d, t| {
        radd(d, t, a1)
    });
    let m_term_n5_plus_a1 = radd(d, m_term_plus_n5, a1);
    let assoc_we = d.lemma(rat.add_assoc, &[m_term, n5_idx, a1]);
    let n5_plus_a1 = radd(d, n5_idx, a1);
    let m_term_plus_n5a1 = radd(d, m_term, n5_plus_a1);
    let eq_we_full = rtrans(
        d,
        with_extra_target,
        m_term_n5_plus_a1,
        m_term_plus_n5a1,
        eq_we_pre,
        assoc_we,
    );
    let (k, eq_f) = fuse_nds(d, p, n5, one_nat, jj1);
    let k_idx = nds(d, p, k, jj1);
    let eq_we_inner = rcongr(d, n5_plus_a1, k_idx, eq_f, &|d, t| radd(d, m_term, t));
    let m_term_plus_k = radd(d, m_term, k_idx);
    let eq_with_extra = rtrans(
        d,
        with_extra_target,
        m_term_plus_n5a1,
        m_term_plus_k,
        eq_we_full,
        eq_we_inner,
    );

    let with_extra_actual = radd(d, bnd_leg_actual, a1);
    let final_le = rat_eq_rewrite(
        d,
        with_extra_target,
        m_term_plus_k,
        eq_with_extra,
        with_extra_le,
        &|d, t| rle(d, rat, with_extra_actual, t),
    );

    (k, final_le)
}

#[cfg(test)]
mod bnd_leg_plus_share_le_at_tests {
    use super::*;
    use crate::Declaration;

    /// The raw bound, symbolic in `a b e jj1 m magnitude`, closed into a
    /// real `Theorem`. `bound_at_idx` is built literally as `radd(sample_te,
    /// b1)` (the zero-step-defeq case the doc comment names), since this
    /// leg has no real `riemann_sum_integral_close`-shaped caller yet — the
    /// construction under test is `bnd_leg_plus_share_le_at` itself, not a
    /// hand-built stand-in for a future caller.
    #[test]
    fn bnd_leg_plus_share_le_at_proves_the_stated_bound() {
        crate::on_a_deep_stack(bnd_leg_plus_share_le_at_proves_the_stated_bound_body);
    }

    fn bnd_leg_plus_share_le_at_proves_the_stated_bound_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();
        let carrier = creal_ty(&mut d, p);

        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let jj1_fv = d.fresh_fvar();
        let jj1 = d.kernel().fvar(jj1_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);

        // `magnitude` is NOT an independent free input: `total_eps_sample_le_at`
        // (via `riemann_sum_total_eps_le`) embeds `succ(CReal.bound(width_of(a,b)))`
        // in its own conclusion, so the caller's `magnitude` must be that SAME
        // `ExprId` (hash-consed), exactly the recipe `total_eps_sample_le_at`'s
        // own test uses — an unrelated `magnitude` fails to type-check.
        let width = width_of(&mut d, p, a, b);
        let (_c, magnitude, _width_le) = direct_bound_le(&mut d, p, width);

        let total_eps = total_eps_of(&mut d, p, a, b, e, m);
        let sample_te = sample(&mut d, p, total_eps, jj1);
        let b1 = div_succ(&mut d, p, 2, jj1);
        let bound_at_idx = radd(&mut d, sample_te, b1);

        let (k, proof) =
            bnd_leg_plus_share_le_at(&mut d, p, a, b, e, jj1, m, magnitude, bound_at_idx);

        let a1 = div_succ(&mut d, p, 1, jj1);
        let shift_jj1 = shift(&mut d, jj1);
        let modulus_idx_shift = modulus(&mut d, p, jj1, shift_jj1);
        let modulus_shift_idx = modulus(&mut d, p, shift_jj1, jj1);
        let part1_actual = radd(&mut d, modulus_idx_shift, bound_at_idx);
        let bnd_leg_actual = radd(&mut d, part1_actual, modulus_shift_idx);
        let with_extra_actual = radd(&mut d, bnd_leg_actual, a1);
        let m_term = nds(&mut d, p, magnitude, e);
        let k_idx = nds(&mut d, p, k, jj1);
        let target = radd(&mut d, m_term, k_idx);
        let concl_ty = rle(&mut d, p.rat, with_extra_actual, target);

        // `Kernel::infer` on the unwrapped `proof` hits `UnboundFVar` (the
        // free variables of `bnd_leg_plus_share_le_at`'s own construction) —
        // close over them into a real `Theorem` first, `declare_of_nat_le`'s
        // own idiom, and let `add_declaration` be the check. `magnitude` is
        // NOT separately quantified: it is a term built from `a`/`b`, not an
        // independent input.
        let ty = {
            let over_m = d.pi_fv(m_fv, nat, concl_ty);
            let over_jj1 = d.pi_fv(jj1_fv, nat, over_m);
            let over_e = d.pi_fv(e_fv, nat, over_jj1);
            let over_b = d.pi_fv(b_fv, carrier, over_e);
            d.pi_fv(a_fv, carrier, over_b)
        };
        let value = {
            let over_m = d.lam_fv(m_fv, nat, proof);
            let over_jj1 = d.lam_fv(jj1_fv, nat, over_m);
            let over_e = d.lam_fv(e_fv, nat, over_jj1);
            let over_b = d.lam_fv(b_fv, carrier, over_e);
            d.lam_fv(a_fv, carrier, over_b)
        };

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "bndLegPlusShareLeAtStatedBoundSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "bnd_leg_plus_share_le_at must prove the stated bound, closed over a b e jj1 m: {:?}",
            result.err()
        );
    }

    /// Non-vacuity, aimed at the specific thing this generalization adds:
    /// swapping `e` and `jj1` must change the rendered target, since `e`
    /// appears ONLY in `m_term` and `jj1` appears ONLY in the folded
    /// `natDivSucc(k,jj1)` side. If swapping them rendered identically, the
    /// construction would be silently collapsing back to the shared-index
    /// case rather than genuinely separating the two indices.
    #[test]
    fn bnd_leg_plus_share_le_at_is_not_symmetric_in_e_and_jj1() {
        crate::on_a_deep_stack(bnd_leg_plus_share_le_at_is_not_symmetric_in_e_and_jj1_body);
    }

    fn bnd_leg_plus_share_le_at_is_not_symmetric_in_e_and_jj1_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let a = d.kernel().const_(p.zero, vec![]);
        let b = d.kernel().const_(p.one, vec![]);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let jj1_fv = d.fresh_fvar();
        let jj1 = d.kernel().fvar(jj1_fv);
        let m = d.num(6);
        // `magnitude` must be the SAME `ExprId` `riemann_sum_total_eps_le`
        // embeds internally (`succ(CReal.bound(width_of(a,b)))`), not an
        // arbitrary literal — see `bnd_leg_plus_share_le_at_proves_the_stated_bound`.
        let width = width_of(&mut d, p, a, b);
        let (_c, magnitude, _width_le) = direct_bound_le(&mut d, p, width);

        let render_target_for = |d: &mut IntDev<'_>, e: ExprId, jj1: ExprId| -> String {
            let total_eps = total_eps_of(d, p, a, b, e, m);
            let sample_te = sample(d, p, total_eps, jj1);
            let b1 = div_succ(d, p, 2, jj1);
            let bound_at_idx = radd(d, sample_te, b1);
            let (k, _proof) =
                bnd_leg_plus_share_le_at(d, p, a, b, e, jj1, m, magnitude, bound_at_idx);
            let m_term = nds(d, p, magnitude, e);
            let k_idx = nds(d, p, k, jj1);
            let target = radd(d, m_term, k_idx);
            d.kernel().render_lean(target)
        };

        let straight = render_target_for(&mut d, e, jj1);
        let swapped = render_target_for(&mut d, jj1, e);
        assert_ne!(
            straight, swapped,
            "swapping e/jj1 must change the rendered target"
        );
    }

    /// Concrete instantiation: `e := 6`, `jj1 := 3`, `m := 6`, `a := zero`,
    /// `b := one`, `magnitude := succ(CReal.bound(width_of(a,b)))` (the
    /// correct derived value — see the stated-bound test's own doc comment
    /// for why an arbitrary literal does not type-check). `k` must be defeq
    /// to the literal `9`, matching
    /// [`bnd_leg_plus_share_le`]'s own doc-commented leaf count with the
    /// `magnitude` term now carried separately rather than folded in.
    #[test]
    fn bnd_leg_plus_share_le_at_k_is_nine_at_concrete_inputs() {
        crate::on_a_deep_stack(bnd_leg_plus_share_le_at_k_is_nine_at_concrete_inputs_body);
    }

    fn bnd_leg_plus_share_le_at_k_is_nine_at_concrete_inputs_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let a = d.kernel().const_(p.zero, vec![]);
        let b = d.kernel().const_(p.one, vec![]);
        let e = d.num(6);
        let jj1 = d.num(3);
        let m = d.num(6);
        let width = width_of(&mut d, p, a, b);
        let (_c, magnitude, _width_le) = direct_bound_le(&mut d, p, width);

        let total_eps = total_eps_of(&mut d, p, a, b, e, m);
        let sample_te = sample(&mut d, p, total_eps, jj1);
        let b1 = div_succ(&mut d, p, 2, jj1);
        let bound_at_idx = radd(&mut d, sample_te, b1);

        let (k, proof) =
            bnd_leg_plus_share_le_at(&mut d, p, a, b, e, jj1, m, magnitude, bound_at_idx);

        d.kernel()
            .infer(proof)
            .expect("bnd_leg_plus_share_le_at's proof must type-check at concrete inputs");

        let nine = d.num(9);
        assert!(
            d.kernel().def_eq(k, nine),
            "k must be defeq to the literal 9 at concrete inputs, matching \
             bnd_leg_plus_share_le's own `magnitude + 9` leaf count"
        );
    }
}

/// `CReal.riemannSumDeepCauchyFolded : ∀ F a b, CReal.le a b →
/// CReal.UniformlyContinuousOn F a b → ∀ p q : Nat, Within (seq (riemannSum
/// F a b (deep F a b u p)) p − seq (riemannSum F a b (deep F a b u q)) q)
/// (Rat.natDivSucc K p + Rat.natDivSucc K q)` -- folding
/// [`CRealPrelude::riemann_sum_deep_cauchy`]'s three-leg `bound(p,q)` into
/// the literal `Cauchy`-rate shape [`CRealPrelude::regular_of_scaled_cauchy`]
/// needs, via [`bnd_leg_plus_share_le`] applied once at each side plus one
/// `Rat` associativity/commutativity reassociation absorbing the shared
/// `modulus(p,q)` leg into each side's own bundle. See
/// [`bnd_leg_plus_share_le`]'s doc comment for the exact leaf accounting.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_deep_cauchy_folded(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);
    let rat = p.rat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let pn_fv = d.fresh_fvar();
    let pn = d.kernel().fvar(pn_fv);
    let qn_fv = d.fresh_fvar();
    let qn = d.kernel().fvar(qn_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    // raw : Within diff final_bound -- `riemannSumDeepCauchy` itself. Its
    // own binder order is `F a b p q hab u` (see that declaration's `ty`
    // construction), NOT `F a b hab u p q`.
    let raw = d.lemma(p.riemann_sum_deep_cauchy, &[f, a, b, pn, qn, hab, u]);

    // Reconstruct `deep_at`'s two witnesses and their `+0` shape, EXACTLY as
    // `declare_riemann_sum_deep_cauchy` does, so the pieces below match
    // `raw`'s own conclusion type on the nose.
    let deep1 = deep_at(d, p, f, a, b, u, pn);
    let deep2 = deep_at(d, p, f, a, b, u, qn);
    let zero1 = d.num(0);
    let m1 = NatOps::add(d, deep1, zero1);
    let zero2 = d.num(0);
    let m2 = NatOps::add(d, deep2, zero2);

    let rsum_m1 = rsum(d, p, f, a, b, m1);
    let rsum_m2 = rsum(d, p, f, a, b, m2);
    let x_val = sample(d, p, rsum_m1, pn);
    let w_val = sample(d, p, rsum_m2, qn);
    let diff = rsub(d, rat, x_val, w_val);

    let width = width_of(d, p, a, b);
    let (_c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);

    let bound1_fn = shared_accuracy_bound_fn(d, p, a, b, pn, m1);
    let bound2_fn = shared_accuracy_bound_fn(d, p, a, b, qn, m2);
    let bound1_pn = d.apply(bound1_fn, &[pn]);
    let bound2_qn = d.apply(bound2_fn, &[qn]);

    let shift_pn = shift(d, pn);
    let m_pn_spn = modulus(d, p, pn, shift_pn);
    let m_spn_pn = modulus(d, p, shift_pn, pn);
    let bnd_a = {
        let inner = radd(d, m_pn_spn, bound1_pn);
        radd(d, inner, m_spn_pn)
    };

    let bnd_b = modulus(d, p, pn, qn);

    let shift_qn = shift(d, qn);
    let m_qn_sqn = modulus(d, p, qn, shift_qn);
    let m_sqn_qn = modulus(d, p, shift_qn, qn);
    let bnd_c = {
        let inner = radd(d, m_qn_sqn, bound2_qn);
        radd(d, inner, m_sqn_qn)
    };

    let final_bound = {
        let ab = radd(d, bnd_a, bnd_b);
        radd(d, ab, bnd_c)
    };

    let (k, leg_p_le) = bnd_leg_plus_share_le(d, p, a, b, pn, m1, magnitude, bound1_pn);
    let (_k_q, leg_q_le) = bnd_leg_plus_share_le(d, p, a, b, qn, m2, magnitude, bound2_qn);

    let mb_p = div_succ(d, p, 1, pn);
    let mb_q = div_succ(d, p, 1, qn);

    // final_bound = (bnd_a + (mb_p+mb_q)) + bnd_c  =  (bnd_a+mb_p) + (bnd_c+mb_q).
    let bnd_a_plus_mb_p = radd(d, bnd_a, mb_p);
    let bnd_c_plus_mb_q = radd(d, bnd_c, mb_q);
    let mb_q_plus_bnd_c = radd(d, mb_q, bnd_c);
    let bnd_a_plus_mb_p_plus_mb_q = radd(d, bnd_a_plus_mb_p, mb_q);

    let bnd_a_plus_bnd_b = radd(d, bnd_a, bnd_b);
    let step1_eq = {
        let assoc = d.lemma(rat.add_assoc, &[bnd_a, mb_p, mb_q]);
        // assoc : Eq (radd(radd(bnd_a,mb_p),mb_q)) (radd(bnd_a,bnd_b))
        rsymm(d, bnd_a_plus_mb_p_plus_mb_q, bnd_a_plus_bnd_b, assoc)
    };
    let step1_full = rcongr(
        d,
        bnd_a_plus_bnd_b,
        bnd_a_plus_mb_p_plus_mb_q,
        step1_eq,
        &|d, t| radd(d, t, bnd_c),
    );
    let step2_eq = d.lemma(rat.add_assoc, &[bnd_a_plus_mb_p, mb_q, bnd_c]);
    let step3_eq = d.lemma(rat.add_comm, &[mb_q, bnd_c]);
    let step3_full = rcongr(d, mb_q_plus_bnd_c, bnd_c_plus_mb_q, step3_eq, &|d, t| {
        radd(d, bnd_a_plus_mb_p, t)
    });

    let mid1 = radd(d, bnd_a_plus_mb_p_plus_mb_q, bnd_c);
    let mid2 = radd(d, bnd_a_plus_mb_p, mb_q_plus_bnd_c);
    let mid3 = radd(d, bnd_a_plus_mb_p, bnd_c_plus_mb_q);
    let (_, reassoc_eq) = rchain(
        d,
        final_bound,
        &[(mid1, step1_full), (mid2, step2_eq), (mid3, step3_full)],
    );

    let k_pn = nds(d, p, k, pn);
    let k_qn = nds(d, p, k, qn);
    let regrouped_le = d.lemma(
        rat.add_le_add,
        &[
            bnd_a_plus_mb_p,
            k_pn,
            bnd_c_plus_mb_q,
            k_qn,
            leg_p_le,
            leg_q_le,
        ],
    );

    let target = radd(d, k_pn, k_qn);
    let reassoc_eq_symm = rsymm(d, final_bound, mid3, reassoc_eq);
    let final_order = rat_eq_rewrite(
        d,
        mid3,
        final_bound,
        reassoc_eq_symm,
        regrouped_le,
        &|d, t| rle(d, rat, t, target),
    );

    let proof = weaken(d, p, diff, final_bound, target, raw, final_order);

    let concl_ty = within(d, p, diff, target);

    let ty = {
        let after_u = d.pi_fv(u_fv, u_ty, concl_ty);
        let after_hab = d.arrow(hab_ty, after_u);
        let over_qn = d.pi_fv(qn_fv, nat, after_hab);
        let over_pn = d.pi_fv(pn_fv, nat, over_qn);
        let over_b = d.pi_fv(b_fv, carrier, over_pn);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_u = d.lam_fv(u_fv, u_ty, proof);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_qn = d.lam_fv(qn_fv, nat, with_hab);
        let over_pn = d.lam_fv(pn_fv, nat, over_qn);
        let over_b = d.lam_fv(b_fv, carrier, over_pn);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_deep_cauchy_folded,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.riemannSumDeepCauchyCross` -- the SAME three-leg telescope as
// `riemannSumDeepCauchy`, specialized to ONE shared sample index `n` (`pn :=
// qn := n`, so the middle `regular` leg becomes trivially `regular rsum_l n
// n`) but generalized to TWO INDEPENDENT uniform-continuity witnesses `u1`,
// `u2` for `F` (`riemannSumDeepCauchy` uses the SAME `u` on both sides).
// This is the witness/modulus reindexing bridge
// `docs/formalized-math-2026-08`'s open question on `CReal.integral` asks
// for: nothing in `riemann_sum_cauchy`, `shared_index_to_canonical`, or
// `common_refinement` is specific to a SINGLE witness -- `riemann_sum_cauchy`
// is already `∀ u, …`, `shared_index_to_canonical` never mentions `u` at
// all, and `common_refinement` is pure `Nat` arithmetic on `m1`/`m2` however
// they were built -- so using `u1` for the `m1` leg and `u2` for the `m2`
// leg is the exact same construction with one fvar duplicated into two. ---

/// `CReal.riemannSumDeepCauchyCross : ∀ F a b, CReal.le a b → ∀ u1 u2 :
/// CReal.UniformlyContinuousOn F a b, ∀ n : Nat, Within (Rat.sub (seq
/// (riemannSum F a b (deep F a b u1 n)) n) (seq (riemannSum F a b (deep F a
/// b u2 n)) n)) (bound n)`, `deep` computed exactly as [`deep_at`] does,
/// `bound n := (modulus(n, shift n) + bound1_fn n + modulus(shift n, n)) +
/// modulus(n, n) + (modulus(n, shift n) + bound2_fn n + modulus(shift n,
/// n))` -- [`declare_riemann_sum_deep_cauchy`]'s own `bnd_a + bnd_b + bnd_c`
/// at `pn = qn = n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_deep_cauchy_cross(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u1_fv = d.fresh_fvar();
    let u1 = d.kernel().fvar(u1_fv);
    let u2_fv = d.fresh_fvar();
    let u2 = d.kernel().fvar(u2_fv);

    let deep1 = deep_at(d, p, f, a, b, u1, n);
    let deep2 = deep_at(d, p, f, a, b, u2, n);
    let zero1 = d.num(0);
    let m1 = NatOps::add(d, deep1, zero1);
    let zero2 = d.num(0);
    let m2 = NatOps::add(d, deep2, zero2);

    let h1 = d.lemma(p.riemann_sum_cauchy, &[f, a, b, n, m2, zero1, hab, u1]);
    let h2_raw = d.lemma(p.riemann_sum_cauchy, &[f, a, b, n, m1, zero2, hab, u2]);

    let (l, l2, l2_eq_l) = common_refinement(d, m1, m2);

    let h2 = {
        let rsum_m2_for_motive = rsum(d, p, f, a, b, m2);
        let neg_rsum_m2_for_motive = cneg(d, p, rsum_m2_for_motive);
        nat_rewrite_prop(d, l2, l, l2_eq_l, h2_raw, &|d, x| {
            let rsum_x = rsum(d, p, f, a, b, x);
            let t = cadd(d, p, rsum_x, neg_rsum_m2_for_motive);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let seq_t_i = sample(d, p, t, i);
            let bound_i = shared_accuracy_bound(d, p, a, b, n, m2, i);
            let claim = within(d, p, seq_t_i, bound_i);
            d.pi_fv(i_fv, nat, claim)
        })
    };

    let rsum_l = rsum(d, p, f, a, b, l);
    let rsum_m1 = rsum(d, p, f, a, b, m1);
    let rsum_m2 = rsum(d, p, f, a, b, m2);

    let bound1_fn = shared_accuracy_bound_fn(d, p, a, b, n, m1);
    let bound2_fn = shared_accuracy_bound_fn(d, p, a, b, n, m2);

    let app1 = d.lemma(
        p.shared_index_to_canonical,
        &[rsum_l, rsum_m1, bound1_fn, h1, n, n, n],
    );
    let app2 = d.lemma(
        p.shared_index_to_canonical,
        &[rsum_l, rsum_m2, bound2_fn, h2, n, n, n],
    );

    let x_val = sample(d, p, rsum_m1, n);
    let y_val = sample(d, p, rsum_l, n);
    let z_val = sample(d, p, rsum_l, n);
    let w_val = sample(d, p, rsum_m2, n);

    let shift_n = shift(d, n);
    let m_n_sn = modulus(d, p, n, shift_n);
    let bound1_n = d.apply(bound1_fn, &[n]);
    let m_sn_n = modulus(d, p, shift_n, n);
    let bnd_a_inner = radd(d, m_n_sn, bound1_n);
    let bnd_a = radd(d, bnd_a_inner, m_sn_n);

    let bnd_b = modulus(d, p, n, n);

    let bound2_n = d.apply(bound2_fn, &[n]);
    let bnd_c_inner = radd(d, m_n_sn, bound2_n);
    let bnd_c = radd(d, bnd_c_inner, m_sn_n);

    let leg_a = within_symm(d, p, y_val, x_val, bnd_a, app1);
    let leg_b = d.lemma(p.regular, &[rsum_l, n, n]);
    let leg_c = app2;

    let proof = chain_within3(
        d, p, x_val, y_val, z_val, w_val, bnd_a, bnd_b, bnd_c, leg_a, leg_b, leg_c,
    );

    let final_bound = {
        let ab = radd(d, bnd_a, bnd_b);
        radd(d, ab, bnd_c)
    };
    let concl_ty = {
        let diff = rsub(d, p.rat, x_val, w_val);
        within(d, p, diff, final_bound)
    };

    // Binder order `F a b hab u1 u2 n` (`n` LAST, unlike
    // `riemann_sum_deep_cauchy`'s `F a b p q hab u`) so that applying only
    // `[F, a, b, hab, u1, u2]` leaves a clean `∀ n, …` term —
    // `declare_integral_witness_independent`'s own
    // `riemann_sum_deep_cauchy_cross_folded` application relies on this
    // shape to feed [`CRealPrelude::converges_of_close`] directly.
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, concl_ty);
        let after_u2 = d.pi_fv(u2_fv, u_ty, over_n);
        let after_u1 = d.pi_fv(u1_fv, u_ty, after_u2);
        let after_hab = d.arrow(hab_ty, after_u1);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let with_u2 = d.lam_fv(u2_fv, u_ty, over_n);
        let with_u1 = d.lam_fv(u1_fv, u_ty, with_u2);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u1);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_deep_cauchy_cross,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.riemannSumDeepCauchyCrossFolded : ∀ F a b, CReal.le a b → ∀ u1 u2,
/// ∀ n : Nat, Within (Rat.sub (seq (riemannSum F a b (deep F a b u1 n)) n)
/// (seq (riemannSum F a b (deep F a b u2 n)) n)) (Rat.natDivSucc K n +
/// Rat.natDivSucc K n)` -- [`declare_riemann_sum_deep_cauchy_cross`]'s own
/// three-leg bound folded via [`bnd_leg_plus_share_le`] applied twice at the
/// SAME `idx := n` (once per witness's own `m1`/`m2`), exactly mirroring
/// [`declare_riemann_sum_deep_cauchy_folded`]'s fold at `pn = qn = n`. `K`
/// depends only on `magnitude` (`width_of a b`), so it is the SAME `Nat`
/// `ExprId` on both sides -- and the SAME `K` [`integral_witness`] itself
/// builds, by the identical `fold_k(magnitude)` call.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_deep_cauchy_cross_folded(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);
    let rat = p.rat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u1_fv = d.fresh_fvar();
    let u1 = d.kernel().fvar(u1_fv);
    let u2_fv = d.fresh_fvar();
    let u2 = d.kernel().fvar(u2_fv);

    // raw : Within diff final_bound -- `riemannSumDeepCauchyCross` itself.
    // Its own binder order is `F a b hab u1 u2 n` (`n` LAST -- see that
    // declaration's own doc comment for why).
    let raw = d.lemma(p.riemann_sum_deep_cauchy_cross, &[f, a, b, hab, u1, u2, n]);

    let deep1 = deep_at(d, p, f, a, b, u1, n);
    let deep2 = deep_at(d, p, f, a, b, u2, n);
    let zero1 = d.num(0);
    let m1 = NatOps::add(d, deep1, zero1);
    let zero2 = d.num(0);
    let m2 = NatOps::add(d, deep2, zero2);

    let rsum_m1 = rsum(d, p, f, a, b, m1);
    let rsum_m2 = rsum(d, p, f, a, b, m2);
    let x_val = sample(d, p, rsum_m1, n);
    let w_val = sample(d, p, rsum_m2, n);
    let diff = rsub(d, rat, x_val, w_val);

    let width = width_of(d, p, a, b);
    let (_c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);

    let bound1_fn = shared_accuracy_bound_fn(d, p, a, b, n, m1);
    let bound2_fn = shared_accuracy_bound_fn(d, p, a, b, n, m2);
    let bound1_n = d.apply(bound1_fn, &[n]);
    let bound2_n = d.apply(bound2_fn, &[n]);

    let shift_n = shift(d, n);
    let m_n_sn = modulus(d, p, n, shift_n);
    let m_sn_n = modulus(d, p, shift_n, n);
    let bnd_a = {
        let inner = radd(d, m_n_sn, bound1_n);
        radd(d, inner, m_sn_n)
    };

    let bnd_b = modulus(d, p, n, n);

    let bnd_c = {
        let inner = radd(d, m_n_sn, bound2_n);
        radd(d, inner, m_sn_n)
    };

    let final_bound = {
        let ab = radd(d, bnd_a, bnd_b);
        radd(d, ab, bnd_c)
    };

    let (k, leg_p_le) = bnd_leg_plus_share_le(d, p, a, b, n, m1, magnitude, bound1_n);
    let (_k_q, leg_q_le) = bnd_leg_plus_share_le(d, p, a, b, n, m2, magnitude, bound2_n);

    let mb_n = div_succ(d, p, 1, n);

    // final_bound = (bnd_a + (mb_n+mb_n)) + bnd_c  =  (bnd_a+mb_n) + (bnd_c+mb_n).
    let bnd_a_plus_mb_n = radd(d, bnd_a, mb_n);
    let bnd_c_plus_mb_n = radd(d, bnd_c, mb_n);
    let mb_n_plus_bnd_c = radd(d, mb_n, bnd_c);
    let bnd_a_plus_mb_n_plus_mb_n = radd(d, bnd_a_plus_mb_n, mb_n);

    let bnd_a_plus_bnd_b = radd(d, bnd_a, bnd_b);
    let step1_eq = {
        let assoc = d.lemma(rat.add_assoc, &[bnd_a, mb_n, mb_n]);
        rsymm(d, bnd_a_plus_mb_n_plus_mb_n, bnd_a_plus_bnd_b, assoc)
    };
    let step1_full = rcongr(
        d,
        bnd_a_plus_bnd_b,
        bnd_a_plus_mb_n_plus_mb_n,
        step1_eq,
        &|d, t| radd(d, t, bnd_c),
    );
    let step2_eq = d.lemma(rat.add_assoc, &[bnd_a_plus_mb_n, mb_n, bnd_c]);
    let step3_eq = d.lemma(rat.add_comm, &[mb_n, bnd_c]);
    let step3_full = rcongr(d, mb_n_plus_bnd_c, bnd_c_plus_mb_n, step3_eq, &|d, t| {
        radd(d, bnd_a_plus_mb_n, t)
    });

    let mid1 = radd(d, bnd_a_plus_mb_n_plus_mb_n, bnd_c);
    let mid2 = radd(d, bnd_a_plus_mb_n, mb_n_plus_bnd_c);
    let mid3 = radd(d, bnd_a_plus_mb_n, bnd_c_plus_mb_n);
    let (_, reassoc_eq) = rchain(
        d,
        final_bound,
        &[(mid1, step1_full), (mid2, step2_eq), (mid3, step3_full)],
    );

    let k_n = nds(d, p, k, n);
    let regrouped_le = d.lemma(
        rat.add_le_add,
        &[
            bnd_a_plus_mb_n,
            k_n,
            bnd_c_plus_mb_n,
            k_n,
            leg_p_le,
            leg_q_le,
        ],
    );

    let target = radd(d, k_n, k_n);
    let reassoc_eq_symm = rsymm(d, final_bound, mid3, reassoc_eq);
    let final_order = rat_eq_rewrite(
        d,
        mid3,
        final_bound,
        reassoc_eq_symm,
        regrouped_le,
        &|d, t| rle(d, rat, t, target),
    );

    // Fuse the two SAME-index `natDivSucc` terms into one, so this
    // declaration's own conclusion is the single-term shape
    // `CRealPrelude::converges_of_close`'s cross hypothesis needs directly
    // (no further fusion at the call site in
    // `declare_integral_witness_independent`).
    let two_k = NatOps::add(d, k, k);
    let final_target = nds(d, p, two_k, n);
    let fuse_eq = d.lemma(rat.nat_div_succ_add, &[k, k, n]);
    // fuse_eq : Eq (radd(k_n,k_n)) final_target
    let target_le_final = rat_eq_rewrite(d, target, final_target, fuse_eq, final_order, &|d, t| {
        rle(d, rat, final_bound, t)
    });
    let proof = weaken(d, p, diff, final_bound, final_target, raw, target_le_final);

    let concl_ty = within(d, p, diff, final_target);

    // Binder order `F a b hab u1 u2 n` (`n` LAST), matching
    // `riemannSumDeepCauchyCross`'s own order so
    // `declare_integral_witness_independent` can apply `[F, a, b, hab, u1,
    // u2]` and get a clean `∀ n, …` term back.
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, concl_ty);
        let after_u2 = d.pi_fv(u2_fv, u_ty, over_n);
        let after_u1 = d.pi_fv(u1_fv, u_ty, after_u2);
        let after_hab = d.arrow(hab_ty, after_u1);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let with_u2 = d.lam_fv(u2_fv, u_ty, over_n);
        let with_u1 = d.lam_fv(u1_fv, u_ty, with_u2);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u1);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_deep_cauchy_cross_folded,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.riemannSumAddCauchyCross` -- the THREE-sequence cross telescope
// `integral_add` needs, per this file's module documentation's 2026-08-26
// entry: `riemannSum (F+G)` at its OWN combo-witness's mesh, bridged to
// `riemannSum F` and `riemannSum G` at THEIR OWN (generally different)
// meshes, at a common sample index `n`. `riemannSum_add`'s exact per-`m`
// identity only fires once all three mesh counts agree, so this needs
// [`common_refinement3`] (three counts, not two) plus TWO extra "shift"
// legs `riemannSumDeepCauchyCross` never needed, because THAT telescope
// never compares two DIFFERENT sequences through `CReal.add` -- `CReal.add`
// itself shifts its index (`seq (add x y) n` unfolds to `seq x (shift n) +
// seq y (shift n)`), so bridging `riemannSum_add`'s value at `L` (sampled at
// `shift n`, forced by that shift) back to the plain sample at `n` needs one
// more `CReal.regular` self-bridge per function, EXACTLY the move
// `convergence.rs`'s `declare_converges_add` already makes (there inline,
// here via the private `shift_regular_bound`/`shift_regular_le` restated
// above for this sibling module). This declaration goes straight to the
// FOLDED, single-`natDivSucc(K,n)` shape (unlike `riemannSumDeepCauchy`'s
// own Cross/CrossFolded split): every intermediate leg is folded into a
// `natDivSucc` term via [`bnd_leg_plus_share_le`] (the three cauchy legs)
// or is already one (`natDivSucc(2,n)`, the `riemannSum_add`/shift legs) as
// soon as it is built, so no separate raw-bound declaration is needed. ----

/// `CReal.riemannSumAddCauchyCross : ∀ F G a b, CReal.le a b → ∀ uFG : UC
/// (fun t => add (F t) (G t)) a b, ∀ uF : UC F a b, ∀ uG : UC G a b, ∀ n :
/// Nat, Within (Rat.sub (seq (riemannSum (fun t => add (F t) (G t)) a b
/// (deep … uFG n + 0)) n) (Rat.add (seq (riemannSum F a b (deep F a b uF n +
/// 0)) n) (seq (riemannSum G a b (deep G a b uG n + 0)) n))) (Rat.natDivSucc
/// K n)`, `K` built purely from `magnitude := Nat.succ (CReal.bound
/// (width_of a b))` -- independent of `n`, `F`, `G`, `uFG`, `uF`, `uG` --
/// the shape [`CRealPrelude::converges_of_close`] needs directly.
///
/// # The construction
///
/// [`common_refinement3`] gives a single shared mesh `L` refining all three
/// of `m_fg`, `m_f`, `m_g` (the three `deep`-based mesh counts at accuracy
/// `n`). Three [`CRealPrelude::riemann_sum_cauchy`] calls (the `m_fg` leg
/// lands at `L` directly, by construction; the `m_f`/`m_g` legs need a
/// [`nat_rewrite_prop`] through `common_refinement3`'s own `eq2`/`eq3`,
/// exactly [`declare_riemann_sum_deep_cauchy_cross`]'s own `h2` rewrite)
/// plus [`CRealPrelude::shared_index_to_canonical`] bring each to a plain
/// sample-at-`n` bound, immediately folded via [`bnd_leg_plus_share_le`]
/// (after stripping its extra `natDivSucc(1,idx)` slack via
/// [`le_add_nonneg_right`]) into `natDivSucc(k_fg,n)` / `natDivSucc(k_f,n)`
/// / `natDivSucc(k_g,n)`.
///
/// [`CRealPrelude::riemann_sum_add`] applied at `L`, evaluated at `n`
/// ([`shift_regular_bound`] bridging the `shift n` its own `CReal.add`
/// forces back to plain `n` on each side), combines with the two folded
/// `m_f`/`m_g` legs via [`chain_within2`]/[`chain_within2_pair`] into a
/// single bound between `seq (riemannSum (F+G) a b L) n` and the TARGET sum
/// `seq (riemannSum F a b m_f) n + seq (riemannSum G a b m_g) n`, and the
/// folded `m_fg` leg closes the final gap back to `seq (riemannSum (F+G) a
/// b m_fg) n`. Every combining step re-fuses its two-`natDivSucc` bound into
/// one via [`fuse_nds`], so the declared conclusion is already the single
/// `natDivSucc(K,n)` shape.
///
/// The single `Rat.natDivSucc K n` coefficient
/// [`declare_riemann_sum_add_cauchy_cross`]'s own conclusion folds down to,
/// computed directly from `magnitude` alone. Every [`fuse_nds`] call in that
/// declaration's own construction returns a pair whose `.0` is a bare
/// `NatOps::add` that never touches its `idx` argument (`fuse_nds(d, p, a,
/// b, idx).0 == NatOps::add(d, a, b)`, by inspection of `fuse_nds` itself),
/// and [`bnd_leg_plus_share_le`]'s own returned `k` is, by the SAME
/// argument, exactly [`fold_k`]`(magnitude)` — independent of `idx`/`m`/
/// `bound_at_idx`, hence identical across the FG/F/G legs. So recomputing
/// the declaration's own `k_fg -> k_f2/k_g2 -> k_sides -> k_mid -> k_final
/// -> k_shift2 -> k_grand` chain here with bare `NatOps::add` (no `idx`, no
/// proof) reaches the IDENTICAL `ExprId`, via hash-consing, that the
/// declaration's own kernel-checked proof term mentions. Extracted so
/// [`declare_integral_add`] can supply
/// [`CRealPrelude::converges_of_close`]'s explicit `Kc` argument without a
/// second, independently-drifting copy of this arithmetic.
fn add_cauchy_cross_k(d: &mut IntDev<'_>, magnitude: ExprId) -> ExprId {
    let k_leg = fold_k(d, magnitude);
    let two_nat = d.num(2);
    let k_f2 = NatOps::add(d, two_nat, k_leg);
    let k_sides = NatOps::add(d, k_f2, k_f2);
    let k_mid = NatOps::add(d, two_nat, k_sides);
    let k_final = NatOps::add(d, k_leg, k_mid);
    let k_shift2 = NatOps::add(d, two_nat, two_nat);
    NatOps::add(d, k_final, k_shift2)
}

/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_add_cauchy_cross(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);
    let rat = p.rat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    // combined := fun t => add (F t) (G t) -- EXACTLY `riemannSum_add`'s own
    // shape (`declare_riemann_sum_add`'s `combined` builder).
    let combined = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let gt = d.apply(g, &[t]);
        let body = cadd(d, p, ft, gt);
        d.lam_fv(t_fv, carrier, body)
    };

    let ufg_ty = d.const_app(p.uniformly_continuous_on, &[combined, a, b]);
    let ufg_fv = d.fresh_fvar();
    let ufg = d.kernel().fvar(ufg_fv);
    let uf_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let uf_fv = d.fresh_fvar();
    let uf = d.kernel().fvar(uf_fv);
    let ug_ty = d.const_app(p.uniformly_continuous_on, &[g, a, b]);
    let ug_fv = d.fresh_fvar();
    let ug = d.kernel().fvar(ug_fv);

    // m_fg, m_f, m_g -- the three `deep`-based mesh counts at accuracy `n`,
    // `+0` depth, EXACTLY `integral_witness`'s own per-function `f_lambda`
    // mesh shape.
    let deep_fg = deep_at(d, p, combined, a, b, ufg, n);
    let zero1 = d.num(0);
    let m_fg = NatOps::add(d, deep_fg, zero1);
    let deep_f = deep_at(d, p, f, a, b, uf, n);
    let zero2 = d.num(0);
    let m_f = NatOps::add(d, deep_f, zero2);
    let deep_g = deep_at(d, p, g, a, b, ug, n);
    let zero3 = d.num(0);
    let m_g = NatOps::add(d, deep_g, zero3);

    let (l_val, n_refine_fg, n_refine_f, eq_f, n_refine_g, eq_g) =
        common_refinement3(d, m_fg, m_f, m_g);

    // --- leg FG: direct, m_prime = l_val by construction, no rewrite. ----
    let h_fg = d.lemma(
        p.riemann_sum_cauchy,
        &[combined, a, b, n, n_refine_fg, zero1, hab, ufg],
    );

    // --- leg F: rewrite m_prime = l(n_refine_f,m_f) to l_val via eq_f. ---
    let h_f_raw = d.lemma(
        p.riemann_sum_cauchy,
        &[f, a, b, n, n_refine_f, zero2, hab, uf],
    );
    let l_nf_mf = succ_mul_succ(d, n_refine_f, m_f).0;
    let eq_f_symm = NatOps::symm(d, l_val, l_nf_mf, eq_f);
    let h_f = {
        let rsum_mf_for_motive = rsum(d, p, f, a, b, m_f);
        let neg_rsum_mf_for_motive = cneg(d, p, rsum_mf_for_motive);
        nat_rewrite_prop(d, l_nf_mf, l_val, eq_f_symm, h_f_raw, &|d, x| {
            let rsum_x = rsum(d, p, f, a, b, x);
            let t = cadd(d, p, rsum_x, neg_rsum_mf_for_motive);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let seq_t_i = sample(d, p, t, i);
            let bound_i = shared_accuracy_bound(d, p, a, b, n, m_f, i);
            let claim = within(d, p, seq_t_i, bound_i);
            d.pi_fv(i_fv, nat, claim)
        })
    };

    // --- leg G: rewrite m_prime = l(n_refine_g,m_g) to l_val via eq_g. ---
    let h_g_raw = d.lemma(
        p.riemann_sum_cauchy,
        &[g, a, b, n, n_refine_g, zero3, hab, ug],
    );
    let l_ng_mg = succ_mul_succ(d, n_refine_g, m_g).0;
    let eq_g_symm = NatOps::symm(d, l_val, l_ng_mg, eq_g);
    let h_g = {
        let rsum_mg_for_motive = rsum(d, p, g, a, b, m_g);
        let neg_rsum_mg_for_motive = cneg(d, p, rsum_mg_for_motive);
        nat_rewrite_prop(d, l_ng_mg, l_val, eq_g_symm, h_g_raw, &|d, x| {
            let rsum_x = rsum(d, p, g, a, b, x);
            let t = cadd(d, p, rsum_x, neg_rsum_mg_for_motive);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let seq_t_i = sample(d, p, t, i);
            let bound_i = shared_accuracy_bound(d, p, a, b, n, m_g, i);
            let claim = within(d, p, seq_t_i, bound_i);
            d.pi_fv(i_fv, nat, claim)
        })
    };

    // --- shared_index_to_canonical, at (n,n,n), for all three. ----------
    let rsum_fg_l = rsum(d, p, combined, a, b, l_val);
    let rsum_fg_mfg = rsum(d, p, combined, a, b, m_fg);
    let bound_fg_fn = shared_accuracy_bound_fn(d, p, a, b, n, m_fg);
    let app_fg = d.lemma(
        p.shared_index_to_canonical,
        &[rsum_fg_l, rsum_fg_mfg, bound_fg_fn, h_fg, n, n, n],
    );

    let rsum_f_l = rsum(d, p, f, a, b, l_val);
    let rsum_f_mf = rsum(d, p, f, a, b, m_f);
    let bound_f_fn = shared_accuracy_bound_fn(d, p, a, b, n, m_f);
    let app_f = d.lemma(
        p.shared_index_to_canonical,
        &[rsum_f_l, rsum_f_mf, bound_f_fn, h_f, n, n, n],
    );

    let rsum_g_l = rsum(d, p, g, a, b, l_val);
    let rsum_g_mg = rsum(d, p, g, a, b, m_g);
    let bound_g_fn = shared_accuracy_bound_fn(d, p, a, b, n, m_g);
    let app_g = d.lemma(
        p.shared_index_to_canonical,
        &[rsum_g_l, rsum_g_mg, bound_g_fn, h_g, n, n, n],
    );

    // --- fold each of the three cauchy legs into ONE `natDivSucc(k,n)`. --
    let width = width_of(d, p, a, b);
    let (_c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);
    let one_nat = d.num(1);
    let a1 = div_succ(d, p, 1, n);
    let zero_le_a1 = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, n]);

    let bound_fg_n = d.apply(bound_fg_fn, &[n]);
    let bnd_fg_n = {
        let sn = shift(d, n);
        let m1_ = modulus(d, p, n, sn);
        let m2_ = modulus(d, p, sn, n);
        let inner = radd(d, m1_, bound_fg_n);
        radd(d, inner, m2_)
    };
    let (k_fg, le_fg_full) = bnd_leg_plus_share_le(d, p, a, b, n, m_fg, magnitude, bound_fg_n);
    let bnd_fg_le_a1 = le_add_nonneg_right(d, p, bnd_fg_n, a1, zero_le_a1);
    let bnd_fg_plus_a1 = radd(d, bnd_fg_n, a1);
    let k_fg_n = nds(d, p, k_fg, n);
    let bnd_fg_le_k = d.lemma(
        rat.le_trans,
        &[bnd_fg_n, bnd_fg_plus_a1, k_fg_n, bnd_fg_le_a1, le_fg_full],
    );

    let bound_f_n = d.apply(bound_f_fn, &[n]);
    let bnd_f_n = {
        let sn = shift(d, n);
        let m1_ = modulus(d, p, n, sn);
        let m2_ = modulus(d, p, sn, n);
        let inner = radd(d, m1_, bound_f_n);
        radd(d, inner, m2_)
    };
    let (k_f, le_f_full) = bnd_leg_plus_share_le(d, p, a, b, n, m_f, magnitude, bound_f_n);
    let bnd_f_le_a1 = le_add_nonneg_right(d, p, bnd_f_n, a1, zero_le_a1);
    let bnd_f_plus_a1 = radd(d, bnd_f_n, a1);
    let k_f_n = nds(d, p, k_f, n);
    let bnd_f_le_k = d.lemma(
        rat.le_trans,
        &[bnd_f_n, bnd_f_plus_a1, k_f_n, bnd_f_le_a1, le_f_full],
    );

    let bound_g_n = d.apply(bound_g_fn, &[n]);
    let bnd_g_n = {
        let sn = shift(d, n);
        let m1_ = modulus(d, p, n, sn);
        let m2_ = modulus(d, p, sn, n);
        let inner = radd(d, m1_, bound_g_n);
        radd(d, inner, m2_)
    };
    let (k_g, le_g_full) = bnd_leg_plus_share_le(d, p, a, b, n, m_g, magnitude, bound_g_n);
    let bnd_g_le_a1 = le_add_nonneg_right(d, p, bnd_g_n, a1, zero_le_a1);
    let bnd_g_plus_a1 = radd(d, bnd_g_n, a1);
    let k_g_n = nds(d, p, k_g, n);
    let bnd_g_le_k = d.lemma(
        rat.le_trans,
        &[bnd_g_n, bnd_g_plus_a1, k_g_n, bnd_g_le_a1, le_g_full],
    );

    // Weaken each leg's bound to its folded `natDivSucc`, flipping the FG
    // leg (shared_index_to_canonical gives "L minus base"; the telescope
    // below wants "base minus L" for the FG leg, and "L minus base" for the
    // F/G legs -- see this file's `declare_riemann_sum_deep_cauchy_cross`
    // for the identical asymmetry).
    let q0 = sample(d, p, rsum_fg_mfg, n);
    let q1 = sample(d, p, rsum_fg_l, n);
    let q1_minus_q0 = rsub(d, rat, q1, q0);
    let leg_fg_l_minus_base = weaken(d, p, q1_minus_q0, bnd_fg_n, k_fg_n, app_fg, bnd_fg_le_k);
    let leg_fg = within_symm(d, p, q1, q0, k_fg_n, leg_fg_l_minus_base);
    // leg_fg : Within (q0 - q1) (natDivSucc k_fg n)

    let x_f = sample(d, p, rsum_f_l, n);
    let z_f = sample(d, p, rsum_f_mf, n);
    let x_f_minus_z_f = rsub(d, rat, x_f, z_f);
    let app_f_weak = weaken(d, p, x_f_minus_z_f, bnd_f_n, k_f_n, app_f, bnd_f_le_k);
    // app_f_weak : Within (x_f - z_f) (natDivSucc k_f n)

    let x_g = sample(d, p, rsum_g_l, n);
    let z_g = sample(d, p, rsum_g_mg, n);
    let x_g_minus_z_g = rsub(d, rat, x_g, z_g);
    let app_g_weak = weaken(d, p, x_g_minus_z_g, bnd_g_n, k_g_n, app_g, bnd_g_le_k);
    // app_g_weak : Within (x_g - z_g) (natDivSucc k_g n)

    // --- shift legs: rsum_f_l/rsum_g_l's own regularity, shift n <-> n. --
    let sn = shift(d, n);
    let x_f_shift = sample(d, p, rsum_f_l, sn);
    let x_g_shift = sample(d, p, rsum_g_l, sn);
    let shift_f = shift_regular_bound(d, p, rsum_f_l, n);
    let shift_g = shift_regular_bound(d, p, rsum_g_l, n);

    let two_lit = d.num(2);
    let two_n = div_succ(d, p, 2, n);

    let side_f_raw = chain_within2(d, p, x_f_shift, x_f, z_f, two_n, k_f_n, shift_f, app_f_weak);
    let (k_f2, eq_f2) = fuse_nds(d, p, two_lit, k_f, n);
    let k_f2_n = nds(d, p, k_f2, n);
    let side_f_bound = radd(d, two_n, k_f_n);
    let x_f_shift_minus_z_f = rsub(d, rat, x_f_shift, z_f);
    let side_f = rat_eq_rewrite(d, side_f_bound, k_f2_n, eq_f2, side_f_raw, &|d, t| {
        within(d, p, x_f_shift_minus_z_f, t)
    });

    let side_g_raw = chain_within2(d, p, x_g_shift, x_g, z_g, two_n, k_g_n, shift_g, app_g_weak);
    let (k_g2, eq_g2) = fuse_nds(d, p, two_lit, k_g, n);
    let k_g2_n = nds(d, p, k_g2, n);
    let side_g_bound = radd(d, two_n, k_g_n);
    let x_g_shift_minus_z_g = rsub(d, rat, x_g_shift, z_g);
    let side_g = rat_eq_rewrite(d, side_g_bound, k_g2_n, eq_g2, side_g_raw, &|d, t| {
        within(d, p, x_g_shift_minus_z_g, t)
    });

    // --- combine the two sides: (x_f_shift-z_f)+(x_g_shift-z_g)
    //     = (x_f_shift+x_g_shift) - (z_f+z_g). --------------------------
    let sides_raw = chain_within2_pair(
        d, p, x_f_shift, z_f, x_g_shift, z_g, k_f2_n, k_g2_n, side_f, side_g,
    );
    let (k_sides, eq_sides) = fuse_nds(d, p, k_f2, k_g2, n);
    let k_sides_n = nds(d, p, k_sides, n);
    let sides_bound = radd(d, k_f2_n, k_g2_n);
    let target_sum = radd(d, z_f, z_g);
    let ac_shift_sum = radd(d, x_f_shift, x_g_shift);
    let ac_minus_target = rsub(d, rat, ac_shift_sum, target_sum);
    let sides_combined = rat_eq_rewrite(d, sides_bound, k_sides_n, eq_sides, sides_raw, &|d, t| {
        within(d, p, ac_minus_target, t)
    });

    // --- add-exact leg: `riemannSum_add(F,G,a,b,L)` applied at `n` --
    // relies on `CReal.add`/`CReal.seq`/`CReal.mk`'s own ι-reduction to
    // read `seq (add rsum_f_l rsum_g_l) n` as `x_f_shift + x_g_shift`,
    // EXACTLY the defeq `declare_converges_add`'s own final combining step
    // (`convergence.rs`) already relies on for the identical shape.
    let add_equiv = d.lemma(p.riemann_sum_add, &[f, g, a, b, l_val]);
    let add_eq_n = d.apply(add_equiv, &[n]);
    let add_and_sides_raw = chain_within2(
        d,
        p,
        q1,
        ac_shift_sum,
        target_sum,
        two_n,
        k_sides_n,
        add_eq_n,
        sides_combined,
    );
    let (k_mid, eq_mid) = fuse_nds(d, p, two_lit, k_sides, n);
    let k_mid_n = nds(d, p, k_mid, n);
    let mid_bound = radd(d, two_n, k_sides_n);
    let q1_minus_target = rsub(d, rat, q1, target_sum);
    let add_and_sides =
        rat_eq_rewrite(d, mid_bound, k_mid_n, eq_mid, add_and_sides_raw, &|d, t| {
            within(d, p, q1_minus_target, t)
        });

    // --- final combine: FG-cauchy leg + everything above. ----------------
    let final_raw = chain_within2(
        d,
        p,
        q0,
        q1,
        target_sum,
        k_fg_n,
        k_mid_n,
        leg_fg,
        add_and_sides,
    );
    let (k_final, eq_final) = fuse_nds(d, p, k_fg, k_mid, n);
    let k_final_n = nds(d, p, k_final, n);
    let final_bound = radd(d, k_fg_n, k_mid_n);
    let diff = rsub(d, rat, q0, target_sum);
    let stage1 = rat_eq_rewrite(d, final_bound, k_final_n, eq_final, final_raw, &|d, t| {
        within(d, p, diff, t)
    });
    // stage1 : Within (q0 - target_sum) (natDivSucc k_final n), `target_sum
    // := seq(rsum_f_mf)n + seq(rsum_g_mg)n` -- a PLAIN Rat.add at plain `n`
    // on both samples.

    // --- one more shift correction: `integral_add`'s own `converges_of_close`
    // call compares against `seq (add f_lambda_F f_lambda_G) n` (`CReal.add`
    // shifts its OWN index), not the plain-`n` `target_sum` above -- the
    // IDENTICAL gap the `riemannSum_add` leg above already closed once, one
    // level up (`rsum_f_l`/`rsum_g_l`), now needed again for `rsum_f_mf`/
    // `rsum_g_mg`. Two more [`shift_regular_bound`] calls, flipped and
    // combined via [`chain_within2_pair`], bridge `target_sum` to `seq (add
    // rsum_f_mf rsum_g_mg) n` (read via the SAME ι-reduction as before).
    let z_f_shift = sample(d, p, rsum_f_mf, sn);
    let z_g_shift = sample(d, p, rsum_g_mg, sn);
    let shift_zf = shift_regular_bound(d, p, rsum_f_mf, n);
    // shift_zf : Within (z_f_shift - z_f) (natDivSucc 2 n)
    let shift_zf_flip = within_symm(d, p, z_f_shift, z_f, two_n, shift_zf);
    // shift_zf_flip : Within (z_f - z_f_shift) (natDivSucc 2 n)
    let shift_zg = shift_regular_bound(d, p, rsum_g_mg, n);
    let shift_zg_flip = within_symm(d, p, z_g_shift, z_g, two_n, shift_zg);
    // shift_zg_flip : Within (z_g - z_g_shift) (natDivSucc 2 n)

    let target_sum_shift = radd(d, z_f_shift, z_g_shift);
    let shift_pair_raw = chain_within2_pair(
        d,
        p,
        z_f,
        z_f_shift,
        z_g,
        z_g_shift,
        two_n,
        two_n,
        shift_zf_flip,
        shift_zg_flip,
    );
    // shift_pair_raw : Within (target_sum - target_sum_shift) (2n+2n)
    let (k_shift2, eq_shift2) = fuse_nds(d, p, two_lit, two_lit, n);
    let k_shift2_n = nds(d, p, k_shift2, n);
    let shift_pair_bound = radd(d, two_n, two_n);
    let target_minus_shift = rsub(d, rat, target_sum, target_sum_shift);
    let shift_pair = rat_eq_rewrite(
        d,
        shift_pair_bound,
        k_shift2_n,
        eq_shift2,
        shift_pair_raw,
        &|d, t| within(d, p, target_minus_shift, t),
    );

    let final2_raw = chain_within2(
        d,
        p,
        q0,
        target_sum,
        target_sum_shift,
        k_final_n,
        k_shift2_n,
        stage1,
        shift_pair,
    );
    let (k_grand, eq_grand) = fuse_nds(d, p, k_final, k_shift2, n);
    let k_grand_n = nds(d, p, k_grand, n);
    let grand_bound = radd(d, k_final_n, k_shift2_n);
    // Declared as `seq (add rsum_f_mf rsum_g_mg) n` (a `CReal.add` sample,
    // matching `integral_add`'s own `sumSeq n`'s diagonal EXACTLY), not the
    // raw `target_sum_shift` the proof above was built from -- the SAME
    // ι-reduction bridge as the `riemannSum_add` leg's own `add_eq_n` usage.
    let add_fmf_gmg = cadd(d, p, rsum_f_mf, rsum_g_mg);
    let target_sum_shift_declared = sample(d, p, add_fmf_gmg, n);
    let diff2 = rsub(d, rat, q0, target_sum_shift_declared);
    let proof = rat_eq_rewrite(d, grand_bound, k_grand_n, eq_grand, final2_raw, &|d, t| {
        within(d, p, diff2, t)
    });

    let concl_ty = within(d, p, diff2, k_grand_n);

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, concl_ty);
        let after_ug = d.pi_fv(ug_fv, ug_ty, over_n);
        let after_uf = d.pi_fv(uf_fv, uf_ty, after_ug);
        let after_ufg = d.pi_fv(ufg_fv, ufg_ty, after_uf);
        let after_hab = d.arrow(hab_ty, after_ufg);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_g = d.pi_fv(g_fv, f_ty, over_a);
        d.pi_fv(f_fv, f_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let with_ug = d.lam_fv(ug_fv, ug_ty, over_n);
        let with_uf = d.lam_fv(uf_fv, uf_ty, with_ug);
        let with_ufg = d.lam_fv(ufg_fv, ufg_ty, with_uf);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_ufg);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_g = d.lam_fv(g_fv, f_ty, over_a);
        d.lam_fv(f_fv, f_ty, over_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_add_cauchy_cross,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.integral` -- `regular_of_scaled_cauchy` / `CReal.mk` on the
// `speedup`-reindexed diagonal of `n ↦ riemannSum F a b (deep F a b u n)`.
// Height above `RIEMANN_HEIGHT` (`DERIVED_HEIGHT + 45`) and `CReal.speedup`
// (`DERIVED_HEIGHT + 44`), the two definitions it is built from. -----------

const INTEGRAL_HEIGHT: u16 = DERIVED_HEIGHT + 46;

/// The `Nat` value `K` [`bnd_leg_plus_share_le`] folds into, computed
/// independently of `idx`/`m` (that function's own `K` never depends on
/// either -- see its doc comment). Reproduces the EXACT same `NatOps::add`
/// sequence over the same literals, so calling this with the SAME
/// `magnitude` yields the identical `K` `ExprId` [`declare_riemann_sum_deep_cauchy_folded`]'s
/// own type already carries -- no bridging lemma needed to relate the two.
fn fold_k(d: &mut IntDev<'_>, magnitude: ExprId) -> ExprId {
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let n1 = NatOps::add(d, magnitude, two_nat);
    let n2 = NatOps::add(d, n1, two_nat);
    let n3 = NatOps::add(d, one_nat, one_nat);
    let n4 = NatOps::add(d, n3, n2);
    let n5 = NatOps::add(d, n4, n3);
    NatOps::add(d, n5, one_nat)
}

/// `fun n => CReal.seq (f n) n` -- the raw `Nat -> Rat` diagonal of a
/// `Nat -> CReal` sequence, [`CRealPrelude::regular_of_scaled_cauchy`]'s own
/// shape. Mirrors `convergence.rs`'s private `diagonal` recipe exactly (that
/// helper is private to the sibling `convergence` submodule, so it is not
/// reachable from here -- rebuilt rather than widened for one caller).
fn integral_diagonal(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fn_term = d.apply(f, &[n]);
    let body = sample(d, p, fn_term, n);
    d.lam_fv(n_fv, nat, body)
}

/// Builds `(f_lambda, K, cauchy_proof)`, exactly as [`declare_creal_integral`]
/// itself needs them: `f_lambda := fun n => riemannSum F a b (deep F a b u n
/// + 0)`, `K := fold_k(magnitude)` from `direct_bound_le(width_of(a,b))`, and
/// `cauchy_proof`, a `Within (seq (f_lambda m) m − seq (f_lambda n) n)` bound
/// of `natDivSucc K m + natDivSucc K n` for every `m`/`n`, via
/// `riemannSumDeepCauchyFolded` applied at fresh indices.
///
/// **Extracted so [`declare_integral_converges`] can build the exact same
/// triple, call for call**, rather than risk a syntactically different (even
/// if propositionally equal) reconstruction: `CReal.integral F a b hab u`
/// unfolds to `CReal.mk (speedup (integral_diagonal f_lambda) K) (…)` with
/// THIS `f_lambda`/`K`, so any caller that needs a term whose type mentions
/// `CReal.integral` on the nose must reproduce them identically, and sharing
/// one function is the only way to guarantee that rather than hope for it.
fn integral_witness(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    hab: ExprId,
    u: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let nat = d.nat_ty();

    // f_lambda := fun n => riemannSum F a b (deep F a b u n + 0) -- the
    // raw-indexed sequence `riemannSumDeepCauchyFolded` is itself a Cauchy
    // witness for.
    let f_lambda = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let deep_n = deep_at(d, p, f, a, b, u, n);
        let zero_n = d.num(0);
        let m_n = NatOps::add(d, deep_n, zero_n);
        let rsum_n = rsum(d, p, f, a, b, m_n);
        d.lam_fv(n_fv, nat, rsum_n)
    };

    let width = width_of(d, p, a, b);
    let (_c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);
    let k = fold_k(d, magnitude);

    // cauchy_proof : forall m n, Within (seq (f_lambda m) m - seq (f_lambda
    // n) n) (natDivSucc k m + natDivSucc k n) -- `riemannSumDeepCauchyFolded`
    // applied at FRESH indices, rebound as the outermost binders.
    let cauchy_proof = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let inst = d.lemma(p.riemann_sum_deep_cauchy_folded, &[f, a, b, m, n, hab, u]);
        let with_n = d.lam_fv(n_fv, nat, inst);
        d.lam_fv(m_fv, nat, with_n)
    };

    (f_lambda, k, cauchy_proof)
}

/// `CReal.integral : ∀ F a b, CReal.le a b → CReal.UniformlyContinuousOn F a
/// b → CReal`, defined as `CReal.mk (speedup (diagonal f) K) (regularity
/// proof)`, `f := fun n => riemannSum F a b (deep F a b u n)`, `K` and the
/// regularity proof both supplied by
/// [`CRealPrelude::regular_of_scaled_cauchy`] applied at `f`, `K` (built
/// purely from `magnitude`, [`fold_k`]) and a `Cauchy`-shaped instance of
/// [`CRealPrelude::riemann_sum_deep_cauchy_folded`] at two FRESH indices
/// (rebound as the outermost `∀ m n` `regular_of_scaled_cauchy` itself
/// expects, rather than reusing that theorem's own `p`/`q` binder names --
/// which sit INSIDE `hab`/`u` in its own Pi nesting, not outside them).
///
/// **Kept generic over `(f, K, cauchy_proof)` until this exact point**:
/// `regular_of_scaled_cauchy` is an ALREADY-PROVED theorem, so applying it
/// here is one small `App` node referencing it by name -- it does not
/// re-run or duplicate that theorem's own proof term. Nothing in `K`'s own
/// construction is ever combined via `Nat.mul`/`Nat.add` with the bound
/// index `n` anywhere in this declaration's statement (`K` and `n` are
/// always SIBLING arguments to `Rat.natDivSucc`, never merged) -- unlike the
/// `declare_e_converges` kernel-cost trap this module's own history
/// documents, there is no partial evaluation for a concrete/symbolic mix to
/// desynchronize on.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_creal_integral(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let (f_lambda, k, cauchy_proof) = integral_witness(d, p, f, a, b, hab, u);

    let regularity = d.lemma(p.regular_of_scaled_cauchy, &[f_lambda, k, cauchy_proof]);
    let diag = integral_diagonal(d, p, f_lambda);
    let speedup_term = d.const_app(p.speedup, &[diag, k]);
    let value_body = d.const_app(p.mk, &[speedup_term, regularity]);

    let ty = {
        let after_u = d.arrow(u_ty, carrier);
        let after_hab = d.arrow(hab_ty, after_u);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_u = d.lam_fv(u_fv, u_ty, value_body);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Definition {
        name: p.integral,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(INTEGRAL_HEIGHT),
    })
}

/// `CReal.integral_converges : ∀ F a b hab u, Converges (fun n => riemannSum
/// F a b (Nat.add (deep F a b u n) 0)) (CReal.integral F a b hab u)`.
///
/// Ties `CReal.integral`'s own `mk`/`speedup` construction back to
/// `Converges`, fully generically in `F`/`a`/`b`/`hab`/`u`. Reconstructs the
/// EXACT same `(f_lambda, K, cauchy_proof)` triple [`declare_creal_integral`]
/// itself builds — both call [`integral_witness`], so they cannot drift
/// apart — applies [`CRealPrelude::converges_of_scaled_cauchy`] to it, and
/// states the conclusion as `Converges f_lambda (CReal.integral F a b hab
/// u)` rather than the raw `CReal.mk (…)` term that application actually
/// produces. The kernel accepts the substitution by unfolding
/// `CReal.integral`'s own `Definition` at these exact arguments: since
/// [`declare_creal_integral`] built `CReal.integral` from this very
/// `integral_witness` triple, the two sides are the same term after
/// delta/beta, not merely propositionally equal.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_integral_converges(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let (f_lambda, k, cauchy_proof) = integral_witness(d, p, f, a, b, hab, u);

    let value_body = d.lemma(p.converges_of_scaled_cauchy, &[f_lambda, k, cauchy_proof]);

    let integral_val = d.const_app(p.integral, &[f, a, b, hab, u]);
    let concl = converges_applied(d, p, f_lambda, integral_val);

    // `concl` mentions `hab`/`u` (via `integral_val`), so both must be bound
    // with `pi_fv`, not `d.arrow` — an `arrow` here would leave those fvars
    // unbound (`UnboundFVar`), unlike `declare_creal_integral`'s own `ty`,
    // whose codomain is bare `carrier` and mentions neither.
    let ty = {
        let after_u = d.pi_fv(u_fv, u_ty, concl);
        let after_hab = d.pi_fv(hab_fv, hab_ty, after_u);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_u = d.lam_fv(u_fv, u_ty, value_body);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.integral_converges,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.integral_const : ∀ c a b hab u, Equiv (CReal.integral (fun _ => c)
/// a b hab u) (mul c (add b (neg a)))`.
///
/// The first evaluation law for `CReal.integral`: a constant function's
/// integral is base times height, for the SAME reasons
/// [`declare_riemann_sum_const`] proves it exactly at every subdivision
/// count. Two `Converges` facts about the one `Nat → CReal` sequence
/// `f_lambda := fun n => riemannSum (fun _ => c) a b (deep (fun _ => c) a b u
/// n + 0)`:
///
/// 1. [`declare_integral_converges`] (specialised at `F := fun _ => c`):
///    `Converges f_lambda (CReal.integral (fun _ => c) a b hab u)`.
/// 2. [`CRealPrelude::converges_of_equiv`] applied to
///    [`declare_riemann_sum_const`] instantiated at every deep index in one
///    lambda: `riemannSum (fun _ => c) a b m ~ mul c (b−a)` holds for EVERY
///    `m`, so `f_lambda n ~ mul c (b−a)` for EVERY `n`, and
///    `converges_of_equiv` turns that pointwise fact into `Converges
///    f_lambda (mul c (b−a))` directly (no new estimate — see that
///    declaration's own doc comment for why `K := 2` suffices).
///
/// `CReal.converges_unique` then gives `Equiv (mul c (b−a)) (CReal.integral
/// …)`, and one `Equiv.symm` flips it to the stated direction.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_integral_const(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let f_const = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, c)
    };

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f_const, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let (f_lambda, _k, _cauchy_proof) = integral_witness(d, p, f_const, a, b, hab, u);

    let integral_val = d.const_app(p.integral, &[f_const, a, b, hab, u]);
    let conv_integral = d.lemma(p.integral_converges, &[f_const, a, b, hab, u]);
    // conv_integral : Converges f_lambda integral_val

    let width = width_of(d, p, a, b);
    let target = cmul(d, p, c, width);

    // pointwise : forall n, Equiv (f_lambda n) target -- reconstructing
    // `f_lambda n`'s own `m_n` (deep_at + zero add) so the LHS of each
    // instance is exactly `f_lambda`'s body, not merely defeq to it.
    let pointwise = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let deep_n = deep_at(d, p, f_const, a, b, u, n);
        let zero_n = d.num(0);
        let m_n = NatOps::add(d, deep_n, zero_n);
        let inst = d.lemma(p.riemann_sum_const, &[c, a, b, m_n]);
        // inst : Equiv (riemannSum f_const a b m_n) target
        d.lam_fv(n_fv, nat, inst)
    };

    let conv_target = d.lemma(p.converges_of_equiv, &[f_lambda, target, pointwise]);
    // conv_target : Converges f_lambda target

    let unique = d.lemma(
        p.converges_unique,
        &[f_lambda, target, integral_val, conv_target, conv_integral],
    );
    // unique : Equiv target integral_val

    let proof = d.lemma(p.equiv_symm, &[target, integral_val, unique]);
    // proof : Equiv integral_val target

    let ty_body = equiv(d, p, integral_val, target);

    let value = {
        let with_u = d.lam_fv(u_fv, u_ty, proof);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(c_fv, carrier, over_a)
    };
    // `ty_body` mentions `hab`/`u` (via `integral_val`), so both must be
    // bound with `pi_fv`, not `d.arrow` -- see `declare_integral_converges`'s
    // own `ty` for the identical trap.
    let ty = {
        let after_u = d.pi_fv(u_fv, u_ty, ty_body);
        let after_hab = d.pi_fv(hab_fv, hab_ty, after_u);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(c_fv, carrier, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.integral_const,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.integral_witness_independent : ∀ F a b hab u1 u2, Equiv (CReal.integral
/// F a b hab u1) (CReal.integral F a b hab u2)`.
///
/// **`CReal.integral` is the integral of `F`, not "the integral computed via
/// THIS modulus".** Reconstructs BOTH witnesses' `(f_lambda, K, _)` triples
/// via [`integral_witness`] (`K` is the SAME `ExprId` for both, since it
/// depends only on `width_of a b` — see [`fold_k`]'s doc comment), then:
///
/// 1. `conv1 : Converges f_lambda1 (integral … u1)`,
///    `conv2 : Converges f_lambda2 (integral … u2)` — both
///    [`CRealPrelude::integral_converges`], one per witness.
/// 2. `cross : ∀ n, Within (seq (f_lambda1 n) n − seq (f_lambda2 n) n)
///    (natDivSucc (2K) n)` — [`CRealPrelude::riemann_sum_deep_cauchy_cross_folded`],
///    the cross-witness closeness bound between the two Riemann-sum
///    diagonals at the SAME sample index.
/// 3. [`CRealPrelude::converges_of_close`] transports `conv2` across `cross`:
///    `Converges f_lambda1 (integral … u2)`.
/// 4. [`CRealPrelude::converges_unique`] on `conv1` and step 3 (the SAME
///    sequence `f_lambda1`, two limits): `Equiv (integral … u1) (integral …
///    u2)`.
///
/// No new estimate anywhere — every piece is an already-proved lemma
/// applied at the right arguments.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_integral_witness_independent(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u1_fv = d.fresh_fvar();
    let u1 = d.kernel().fvar(u1_fv);
    let u2_fv = d.fresh_fvar();
    let u2 = d.kernel().fvar(u2_fv);

    let (f_lambda1, k, _cauchy_proof1) = integral_witness(d, p, f, a, b, hab, u1);
    let (f_lambda2, _k2, _cauchy_proof2) = integral_witness(d, p, f, a, b, hab, u2);

    let integral_val1 = d.const_app(p.integral, &[f, a, b, hab, u1]);
    let integral_val2 = d.const_app(p.integral, &[f, a, b, hab, u2]);

    let conv1 = d.lemma(p.integral_converges, &[f, a, b, hab, u1]);
    // conv1 : Converges f_lambda1 integral_val1
    let conv2 = d.lemma(p.integral_converges, &[f, a, b, hab, u2]);
    // conv2 : Converges f_lambda2 integral_val2

    let cross = d.lemma(
        p.riemann_sum_deep_cauchy_cross_folded,
        &[f, a, b, hab, u1, u2],
    );
    // cross : ∀ n, Within (seq (f_lambda1 n) n - seq (f_lambda2 n) n)
    //              (natDivSucc (k+k) n)
    let kc = NatOps::add(d, k, k);

    let step = d.lemma(
        p.converges_of_close,
        &[f_lambda2, f_lambda1, integral_val2, kc, cross, conv2],
    );
    // step : Converges f_lambda1 integral_val2

    let proof = d.lemma(
        p.converges_unique,
        &[f_lambda1, integral_val1, integral_val2, conv1, step],
    );
    // proof : Equiv integral_val1 integral_val2

    let concl = equiv(d, p, integral_val1, integral_val2);

    // `concl` mentions `hab`/`u1`/`u2`, so all three must be bound with
    // `pi_fv`, not `d.arrow` -- the same trap `declare_integral_converges`'s
    // own doc comment names.
    let ty = {
        let after_u2 = d.pi_fv(u2_fv, u_ty, concl);
        let after_u1 = d.pi_fv(u1_fv, u_ty, after_u2);
        let after_hab = d.pi_fv(hab_fv, hab_ty, after_u1);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_u2 = d.lam_fv(u2_fv, u_ty, proof);
        let with_u1 = d.lam_fv(u1_fv, u_ty, with_u2);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u1);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.integral_witness_independent,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.integral_add : ∀ F G a b hab uFG uF uG, Equiv (CReal.integral (fun
/// t => add (F t) (G t)) a b hab uFG) (add (CReal.integral F a b hab uF)
/// (CReal.integral G a b hab uG))`.
///
/// **The integral of a sum is the sum of the integrals.** Reconstructs all
/// three `(f_lambda, K, _)` triples via [`integral_witness`], then:
///
/// 1. `conv_fg : Converges f_lambda_fg (integral … uFG)`, `conv_f`,
///    `conv_g` similarly — three [`CRealPrelude::integral_converges`]
///    applications.
/// 2. `conv_sum : Converges (fun n => add (f_lambda_f n) (f_lambda_g n))
///    (add (integral … uF) (integral … uG))` — [`CRealPrelude::converges_add`]
///    on `conv_f`, `conv_g`.
/// 3. `cross : ∀ n, Within (seq (f_lambda_fg n) n − seq (add (f_lambda_f n)
///    (f_lambda_g n)) n) (natDivSucc K n)` —
///    [`CRealPrelude::riemann_sum_add_cauchy_cross`], the three-sequence
///    cross-bridge, applied at `F, G, a, b, hab, uFG, uF, uG`. This matches
///    `conv_sum`'s own sequence/limit ONLY because [`integral_witness`]'s
///    `f_lambda` is the exact `deep`-based mesh
///    `riemann_sum_add_cauchy_cross`'s own construction also uses — same
///    `deep_at`/`+0` shape, same `n`.
/// 4. [`CRealPrelude::converges_of_close`] transports `conv_sum` across
///    `cross`: `Converges f_lambda_fg (add (integral … uF) (integral … uG))`.
/// 5. [`CRealPrelude::converges_unique`] on `conv_fg` and step 4 (the SAME
///    sequence `f_lambda_fg`, two limits): `Equiv (integral … uFG) (add
///    (integral … uF) (integral … uG))` — the stated conclusion directly,
///    no final `Equiv.symm` needed (unlike
///    [`declare_integral_witness_independent`]).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_integral_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    // combined := fun t => add (F t) (G t) -- EXACTLY
    // `declare_riemann_sum_add_cauchy_cross`'s own `combined` builder, so
    // `integral_witness`'s `f_lambda` at `combined` matches that
    // declaration's own `m_fg`/diagonal bit for bit.
    let combined = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let gt = d.apply(g, &[t]);
        let body = cadd(d, p, ft, gt);
        d.lam_fv(t_fv, carrier, body)
    };

    let ufg_ty = d.const_app(p.uniformly_continuous_on, &[combined, a, b]);
    let ufg_fv = d.fresh_fvar();
    let ufg = d.kernel().fvar(ufg_fv);
    let uf_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let uf_fv = d.fresh_fvar();
    let uf = d.kernel().fvar(uf_fv);
    let ug_ty = d.const_app(p.uniformly_continuous_on, &[g, a, b]);
    let ug_fv = d.fresh_fvar();
    let ug = d.kernel().fvar(ug_fv);

    let (f_lambda_fg, _k_fg, _cauchy_fg) = integral_witness(d, p, combined, a, b, hab, ufg);
    let (f_lambda_f, _k_f, _cauchy_f) = integral_witness(d, p, f, a, b, hab, uf);
    let (f_lambda_g, _k_g, _cauchy_g) = integral_witness(d, p, g, a, b, hab, ug);

    let integral_val_fg = d.const_app(p.integral, &[combined, a, b, hab, ufg]);
    let integral_val_f = d.const_app(p.integral, &[f, a, b, hab, uf]);
    let integral_val_g = d.const_app(p.integral, &[g, a, b, hab, ug]);

    let conv_fg = d.lemma(p.integral_converges, &[combined, a, b, hab, ufg]);
    // conv_fg : Converges f_lambda_fg integral_val_fg
    let conv_f = d.lemma(p.integral_converges, &[f, a, b, hab, uf]);
    // conv_f : Converges f_lambda_f integral_val_f
    let conv_g = d.lemma(p.integral_converges, &[g, a, b, hab, ug]);
    // conv_g : Converges f_lambda_g integral_val_g

    let sum_target = cadd(d, p, integral_val_f, integral_val_g);
    let conv_sum = d.lemma(
        p.converges_add,
        &[
            f_lambda_f,
            f_lambda_g,
            integral_val_f,
            integral_val_g,
            conv_f,
            conv_g,
        ],
    );
    // conv_sum : Converges (fun n => add (f_lambda_f n) (f_lambda_g n)) sum_target

    let cross = d.lemma(
        p.riemann_sum_add_cauchy_cross,
        &[f, g, a, b, hab, ufg, uf, ug],
    );
    // cross : ∀ n, Within (seq (f_lambda_fg n) n
    //              - seq (add (f_lambda_f n) (f_lambda_g n)) n)
    //              (natDivSucc K n)
    let width = width_of(d, p, a, b);
    let (_c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);
    let kc = add_cauchy_cross_k(d, magnitude);

    let sum_seq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f_lambda_f, &[n]);
        let gn_term = d.apply(f_lambda_g, &[n]);
        let added = cadd(d, p, fn_term, gn_term);
        let nat = d.nat_ty();
        d.lam_fv(n_fv, nat, added)
    };

    let step = d.lemma(
        p.converges_of_close,
        &[sum_seq, f_lambda_fg, sum_target, kc, cross, conv_sum],
    );
    // step : Converges f_lambda_fg sum_target

    let proof = d.lemma(
        p.converges_unique,
        &[f_lambda_fg, integral_val_fg, sum_target, conv_fg, step],
    );
    // proof : Equiv integral_val_fg sum_target

    let concl = equiv(d, p, integral_val_fg, sum_target);

    // `concl` mentions `hab`/`uFG`/`uF`/`uG`, so all four must be bound
    // with `pi_fv`, not `d.arrow` -- the same trap
    // `declare_integral_converges`'s own doc comment names.
    let ty = {
        let after_ug = d.pi_fv(ug_fv, ug_ty, concl);
        let after_uf = d.pi_fv(uf_fv, uf_ty, after_ug);
        let after_ufg = d.pi_fv(ufg_fv, ufg_ty, after_uf);
        let after_hab = d.pi_fv(hab_fv, hab_ty, after_ufg);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_g = d.pi_fv(g_fv, f_ty, over_a);
        d.pi_fv(f_fv, f_ty, over_g)
    };
    let value = {
        let with_ug = d.lam_fv(ug_fv, ug_ty, proof);
        let with_uf = d.lam_fv(uf_fv, uf_ty, with_ug);
        let with_ufg = d.lam_fv(ufg_fv, ufg_ty, with_uf);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_ufg);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_g = d.lam_fv(g_fv, f_ty, over_a);
        d.lam_fv(f_fv, f_ty, over_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.integral_add,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.integral_le` -- order passes to the integral. No `Equiv`/
// `converges_unique` bridge is needed here (unlike `integral_add`/
// `integral_witness_independent`): `CReal.converges_le` compares two
// Converges facts at INDEPENDENT limits directly, so the only obstruction is
// getting BOTH sides' native Riemann-sum sequences onto a SHARED mesh depth
// at each accuracy index `n`. `riemann_sum_cauchy` and
// `shared_index_to_canonical` are already `F`-generic (see
// `riemannSumDeepCauchyCross`'s own module comment: "nothing ... is specific
// to a SINGLE witness"), and neither mentions `u`/`f` in a way that forces
// them to agree across the two calls -- so applying `riemann_sum_cauchy` once
// for `F` (refined by `G`'s own depth) and once for `G` (refined by `F`'s own
// depth) reaches a single shared refinement `l(n)`, exactly the way
// `riemannSumDeepCauchyCross` reaches one for a single function at two
// witnesses. -----------------------------------------------------------

/// `CReal.integral_le : ∀ F G a b hab uF uG, (∀ t, le a t → le t b → le (F t)
/// (G t)) → le (CReal.integral F a b hab uF) (CReal.integral G a b hab uG)`.
///
/// # The construction
///
/// 1. `f_lambda_f`/`f_lambda_g` — `F`'s and `G`'s own NATIVE
///    [`integral_witness`] sequences, and `conv_f_native`/`conv_g_native` —
///    [`CRealPrelude::integral_converges`] at each.
/// 2. At a fresh accuracy index `n`: `m1 := deep(F,uF,n)+0`, `m2 :=
///    deep(G,uG,n)+0` (the native mesh depths at `n`, EXACTLY as
///    [`integral_witness`] itself computes them), and `l :=`
///    [`common_refinement`]`(m1,m2)`'s shared refinement target.
/// 3. Two [`CRealPrelude::riemann_sum_cauchy`] calls — `(F, e:=n,
///    n_refine:=m2, k:=0, uF)` lands directly at `l` (`m_prime =
///    succ_mul_succ(m2,m1) = l`); `(G, e:=n, n_refine:=m1, k:=0, uG)` lands
///    at `common_refinement`'s OTHER target `l2`, rewritten onto `l` via
///    [`crate::rat_prelude::ops::nat_rewrite_prop`] — verbatim the
///    `riemannSumDeepCauchyCross` recipe, `F`/`G` in place of that
///    declaration's "same `f`, two witnesses".
/// 4. [`CRealPrelude::shared_index_to_canonical`] at `(n,n,n)` on each,
///    giving `Within (seq(rsum_F(l))n − seq(rsum_F(m1))n) bnd_a` and the `G`
///    analogue `bnd_c` — the SAME single-leg shape
///    [`riemann_sum_deep_cauchy`]'s own `bnd_a`/`bnd_c` legs have.
/// 5. [`bnd_leg_plus_share_le`] folds each leg (plus one extra unwanted
///    `natDivSucc(1,n)` share term that declaration's own signature always
///    adds, dropped here via [`le_add_nonneg_right`] since — unlike
///    `riemannSumDeepCauchyFolded`'s two-sided fold — there is no partner
///    leg on this side to absorb it into) into a single `natDivSucc(K,n)`,
///    then [`weaken`] widens each `Within` to that literal Cauchy-rate
///    shape [`CRealPrelude::converges_of_close`] demands.
/// 6. [`CRealPrelude::converges_of_close`] transports `conv_f_native`
///    across the `F` bound to `Converges new_seq_f (integral F …)`,
///    `new_seq_f(n) := riemannSum F a b l(n)`; the `G` analogue similarly.
/// 7. `new_seq_f(n)` and `new_seq_g(n)` sample the SAME shared mesh `l(n)`,
///    so [`CRealPrelude::riemann_sum_le_on`] applied there is EXACT (no
///    epsilon slack) and supplies [`CRealPrelude::converges_le`]'s pointwise
///    hypothesis directly.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_integral_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let uf_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let uf_fv = d.fresh_fvar();
    let uf = d.kernel().fvar(uf_fv);
    let ug_ty = d.const_app(p.uniformly_continuous_on, &[g, a, b]);
    let ug_fv = d.fresh_fvar();
    let ug = d.kernel().fvar(ug_fv);

    // hfg_ty : ∀ t, le a t → le t b → le (F t) (G t) -- RESTRICTED to [a,b],
    // the exact shape `riemann_sum_le_on` itself takes.
    let hfg_ty = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let gt = d.apply(g, &[t]);
        let concl = cle(d, p, ft, gt);
        let t_le_b = cle(d, p, t, b);
        let after_upper = d.arrow(t_le_b, concl);
        let a_le_t = cle(d, p, a, t);
        let after_lower = d.arrow(a_le_t, after_upper);
        d.pi_fv(t_fv, carrier, after_lower)
    };
    let hfg_fv = d.fresh_fvar();
    let hfg = d.kernel().fvar(hfg_fv);

    // --- native integral_witness triples, and the two Converges facts
    // `converges_of_close` will transport. ---------------------------------
    let (f_lambda_f, _kf_native, _cauchy_f) = integral_witness(d, p, f, a, b, hab, uf);
    let (f_lambda_g, _kg_native, _cauchy_g) = integral_witness(d, p, g, a, b, hab, ug);

    let integral_f_val = d.const_app(p.integral, &[f, a, b, hab, uf]);
    let integral_g_val = d.const_app(p.integral, &[g, a, b, hab, ug]);

    let conv_f_native = d.lemma(p.integral_converges, &[f, a, b, hab, uf]);
    let conv_g_native = d.lemma(p.integral_converges, &[g, a, b, hab, ug]);

    let width = width_of(d, p, a, b);
    let (_c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);

    // --- the shared refinement `l(n)` and the two cross bounds, at a
    // symbolic accuracy index `n`. ------------------------------------------
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let deep_f_n = deep_at(d, p, f, a, b, uf, n);
    let deep_g_n = deep_at(d, p, g, a, b, ug, n);
    let zero1 = d.num(0);
    let m1 = NatOps::add(d, deep_f_n, zero1); // matches f_lambda_f's own internal mesh count
    let zero2 = d.num(0);
    let m2 = NatOps::add(d, deep_g_n, zero2); // matches f_lambda_g's own internal mesh count

    let h1 = d.lemma(p.riemann_sum_cauchy, &[f, a, b, n, m2, zero1, hab, uf]);
    let h2_raw = d.lemma(p.riemann_sum_cauchy, &[g, a, b, n, m1, zero2, hab, ug]);

    let (l, l2, l2_eq_l) = common_refinement(d, m1, m2);

    let h2 = {
        let rsum_m2_for_motive = rsum(d, p, g, a, b, m2);
        let neg_rsum_m2_for_motive = cneg(d, p, rsum_m2_for_motive);
        nat_rewrite_prop(d, l2, l, l2_eq_l, h2_raw, &|d, x| {
            let rsum_x = rsum(d, p, g, a, b, x);
            let t = cadd(d, p, rsum_x, neg_rsum_m2_for_motive);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let seq_t_i = sample(d, p, t, i);
            let bound_i = shared_accuracy_bound(d, p, a, b, n, m2, i);
            let claim = within(d, p, seq_t_i, bound_i);
            d.pi_fv(i_fv, nat, claim)
        })
    };

    let rsum_l_f = rsum(d, p, f, a, b, l);
    let rsum_m1 = rsum(d, p, f, a, b, m1);
    let rsum_l_g = rsum(d, p, g, a, b, l);
    let rsum_m2 = rsum(d, p, g, a, b, m2);

    let bound1_fn = shared_accuracy_bound_fn(d, p, a, b, n, m1);
    let bound2_fn = shared_accuracy_bound_fn(d, p, a, b, n, m2);

    let app1 = d.lemma(
        p.shared_index_to_canonical,
        &[rsum_l_f, rsum_m1, bound1_fn, h1, n, n, n],
    );
    // app1 : Within (seq(rsum_l_f)n - seq(rsum_m1)n) bnd_a
    let app2 = d.lemma(
        p.shared_index_to_canonical,
        &[rsum_l_g, rsum_m2, bound2_fn, h2, n, n, n],
    );
    // app2 : Within (seq(rsum_l_g)n - seq(rsum_m2)n) bnd_c

    let shift_n = shift(d, n);
    let m_n_sn = modulus(d, p, n, shift_n);
    let m_sn_n = modulus(d, p, shift_n, n);

    let bound1_n = d.apply(bound1_fn, &[n]);
    let bnd_a = {
        let inner = radd(d, m_n_sn, bound1_n);
        radd(d, inner, m_sn_n)
    };
    let bound2_n = d.apply(bound2_fn, &[n]);
    let bnd_c = {
        let inner = radd(d, m_n_sn, bound2_n);
        radd(d, inner, m_sn_n)
    };

    // --- fold each single leg into `natDivSucc(K,n)`, dropping the extra
    // `+natDivSucc(1,n)` share `bnd_leg_plus_share_le` always adds (there is
    // no partner leg here to absorb it into). `K` itself is independent of
    // `idx`/`m`/`bound_at_idx` (only `magnitude`), so both calls return the
    // SAME `K` -- see `riemannSumDeepCauchyFolded`'s own precedent for
    // discarding the second call's `K` and reusing the first's. -----------
    let (k, leg_f_extra_le) = bnd_leg_plus_share_le(d, p, a, b, n, m1, magnitude, bound1_n);
    let (_k_g, leg_g_extra_le) = bnd_leg_plus_share_le(d, p, a, b, n, m2, magnitude, bound2_n);
    let k_n = nds(d, p, k, n);

    let one_nat_f = d.num(1);
    let a1_n = div_succ(d, p, 1, n);
    let a1_nonneg_f = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat_f, n]);
    let bnd_a_le_extra = le_add_nonneg_right(d, p, bnd_a, a1_n, a1_nonneg_f);
    let bnd_a_extra = radd(d, bnd_a, a1_n);
    let bnd_a_le_k = d.lemma(
        p.rat.le_trans,
        &[bnd_a, bnd_a_extra, k_n, bnd_a_le_extra, leg_f_extra_le],
    );

    let one_nat_g = d.num(1);
    let a1_n2 = div_succ(d, p, 1, n);
    let a1_nonneg_g = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat_g, n]);
    let bnd_c_le_extra = le_add_nonneg_right(d, p, bnd_c, a1_n2, a1_nonneg_g);
    let bnd_c_extra = radd(d, bnd_c, a1_n2);
    let bnd_c_le_k = d.lemma(
        p.rat.le_trans,
        &[bnd_c, bnd_c_extra, k_n, bnd_c_le_extra, leg_g_extra_le],
    );

    let seq_rsum_l_f_n = sample(d, p, rsum_l_f, n);
    let seq_rsum_m1_n = sample(d, p, rsum_m1, n);
    let diff_f = rsub(d, p.rat, seq_rsum_l_f_n, seq_rsum_m1_n);
    let cross_f_at_n = weaken(d, p, diff_f, bnd_a, k_n, app1, bnd_a_le_k);
    let seq_rsum_l_g_n = sample(d, p, rsum_l_g, n);
    let seq_rsum_m2_n = sample(d, p, rsum_m2, n);
    let diff_g = rsub(d, p.rat, seq_rsum_l_g_n, seq_rsum_m2_n);
    let cross_g_at_n = weaken(d, p, diff_g, bnd_c, k_n, app2, bnd_c_le_k);

    // --- bind `n`: the two cross bounds, the two shared-mesh sequences, and
    // the exact pointwise comparison at the shared mesh. -------------------
    let cross_f = d.lam_fv(n_fv, nat, cross_f_at_n);
    let cross_g = d.lam_fv(n_fv, nat, cross_g_at_n);
    let new_seq_f = d.lam_fv(n_fv, nat, rsum_l_f);
    let new_seq_g = d.lam_fv(n_fv, nat, rsum_l_g);

    let hle_body = d.lemma(p.riemann_sum_le_on, &[f, g, a, b, l, hab, hfg]);
    // hle_body : le (riemannSum F a b l) (riemannSum G a b l) -- EXACT, both
    // sides sampled at the SAME shared mesh `l`.
    let hle_pointwise = d.lam_fv(n_fv, nat, hle_body);

    let step_f = d.lemma(
        p.converges_of_close,
        &[
            f_lambda_f,
            new_seq_f,
            integral_f_val,
            k,
            cross_f,
            conv_f_native,
        ],
    );
    // step_f : Converges new_seq_f integral_f_val
    let step_g = d.lemma(
        p.converges_of_close,
        &[
            f_lambda_g,
            new_seq_g,
            integral_g_val,
            k,
            cross_g,
            conv_g_native,
        ],
    );
    // step_g : Converges new_seq_g integral_g_val

    let final_proof = d.lemma(
        p.converges_le,
        &[
            new_seq_f,
            new_seq_g,
            integral_f_val,
            integral_g_val,
            step_f,
            step_g,
            hle_pointwise,
        ],
    );
    // final_proof : le integral_f_val integral_g_val

    let concl = cle(d, p, integral_f_val, integral_g_val);

    // `concl` mentions `hab`/`uf`/`ug` (via `integral_f_val`/`integral_g_val`),
    // so all three must be bound with `pi_fv`, not `d.arrow` -- the same
    // trap `declare_integral_converges`'s own doc comment names. `hfg`
    // itself does not appear in `concl`, so it alone uses `d.arrow`.
    let ty = {
        let after_hfg = d.arrow(hfg_ty, concl);
        let after_ug = d.pi_fv(ug_fv, ug_ty, after_hfg);
        let after_uf = d.pi_fv(uf_fv, uf_ty, after_ug);
        let after_hab = d.pi_fv(hab_fv, hab_ty, after_uf);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_g = d.pi_fv(g_fv, f_ty, over_a);
        d.pi_fv(f_fv, f_ty, over_g)
    };
    let value = {
        let with_hfg = d.lam_fv(hfg_fv, hfg_ty, final_proof);
        let with_ug = d.lam_fv(ug_fv, ug_ty, with_hfg);
        let with_uf = d.lam_fv(uf_fv, uf_ty, with_ug);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_uf);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_g = d.lam_fv(g_fv, f_ty, over_a);
        d.lam_fv(f_fv, f_ty, over_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.integral_le,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod integral_le_tests {
    use super::*;
    use crate::Declaration;

    /// **Mandatory concrete instantiation, with a negative (swapped)
    /// control.** `F := fun _ => zero`, `G := fun _ => one`, `a := zero`,
    /// `b := one` — `zero != one`, so a bug that swapped the two integral
    /// values in `integral_le`'s conclusion is visible. The SAME proof term
    /// is checked against BOTH the true conclusion `le (integral F a b hab
    /// uF) (integral G a b hab uG)` (must succeed) and the SWAPPED (false)
    /// conclusion `le (integral G …) (integral F …)` (must be REFUSED) — the
    /// same "inverted control" shape `converges_le`'s own test uses
    /// (`convergence.rs`'s `converges_le_concrete_and_negative_control`),
    /// since `integral_le` is built directly on `converges_le` and could
    /// silently inherit a transposed conclusion from it.
    #[test]
    fn integral_le_concrete_and_negative_control() {
        crate::on_a_deep_stack(integral_le_concrete_and_negative_control_body);
    }

    fn integral_le_concrete_and_negative_control_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);

        let zero_c = d.kernel().const_(p.zero, vec![]);
        let one_c = d.kernel().const_(p.one, vec![]);

        let f_const_zero = {
            let ignore_fv = d.fresh_fvar();
            d.lam_fv(ignore_fv, carrier, zero_c)
        };
        let g_const_one = {
            let ignore_fv = d.fresh_fvar();
            d.lam_fv(ignore_fv, carrier, one_c)
        };

        let a = zero_c;
        let b = one_c;
        let lt01 = d.lemma(p.zero_lt_one, &[]);
        let hab = d.lemma(p.le_of_lt, &[zero_c, one_c, lt01]);

        let uf = d.lemma(p.uniformly_continuous_const, &[zero_c, a, b]);
        let ug = d.lemma(p.uniformly_continuous_const, &[one_c, a, b]);

        // hfg : forall t, le a t -> le t b -> le (f_const_zero t) (g_const_one
        // t) -- beta-reduces to `le zero one` at every `t`, via
        // `zero_lt_one`/`le_of_lt`, a genuine (non-vacuous) fact rather than
        // `le_refl` at a single point.
        let hfg = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let a_le_t_ty = cle(&mut d, p, a, t);
            let t_le_b_ty = cle(&mut d, p, t, b);
            let lt01_inner = d.lemma(p.zero_lt_one, &[]);
            let le01 = d.lemma(p.le_of_lt, &[zero_c, one_c, lt01_inner]);
            let upper_fv = d.fresh_fvar();
            let with_upper = d.lam_fv(upper_fv, t_le_b_ty, le01);
            let lower_fv = d.fresh_fvar();
            let with_lower = d.lam_fv(lower_fv, a_le_t_ty, with_upper);
            d.lam_fv(t_fv, carrier, with_lower)
        };

        let proof = d.lemma(
            p.integral_le,
            &[f_const_zero, g_const_one, a, b, hab, uf, ug, hfg],
        );

        let integral_f_val = d.const_app(p.integral, &[f_const_zero, a, b, hab, uf]);
        let integral_g_val = d.const_app(p.integral, &[g_const_one, a, b, hab, ug]);

        let anon = d.kernel().anon();

        // Positive: the TRUE conclusion must be accepted.
        let true_ty = cle(&mut d, p, integral_f_val, integral_g_val);
        let name_ok = d.kernel().name_str(anon, "__integralLeConcreteOk");
        let result_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: name_ok,
            uparams: vec![],
            ty: true_ty,
            value: proof,
        });
        assert!(
            result_ok.is_ok(),
            "integral_le at F := const zero, G := const one, [a,b] := [0,1] \
             must prove `le (integral F...) (integral G...)`: {:?}",
            result_ok.err()
        );

        // Negative control: the SAME proof term, asserted at the SWAPPED
        // (false) conclusion, must be REFUSED.
        let false_ty = cle(&mut d, p, integral_g_val, integral_f_val);
        let name_bad = d.kernel().name_str(anon, "__integralLeConcreteBad");
        let result_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_bad,
            uparams: vec![],
            ty: false_ty,
            value: proof,
        });
        assert!(
            result_bad.is_err(),
            "the SAME proof term must be REFUSED against the swapped \
             (false) conclusion `le (integral G...) (integral F...)`"
        );
    }
}

// --- `CReal.integral_scale` -- pulling a constant factor out of the
// integral. Unlike `integral_add` (THREE witnesses, `common_refinement3`)
// and unlike a from-scratch Lipschitz bound on `CReal.mul` (the obstruction
// this law was originally expected to hit -- `mul_shift` depends on BOTH
// operands' magnitudes), this needs only TWO witnesses -- `uF` for `F`,
// `ucF` for `combined := fun t => mul c (F t)` -- landed on a shared mesh
// via [`common_refinement`], EXACTLY [`declare_integral_le`]'s own recipe
// with `combined` in `G`'s slot, plus ONE exact per-`m` bridge at that
// shared mesh: [`CRealPrelude::mul_riemann_sum`]. `CReal.mul`'s own
// index-shift complexity is never re-derived by hand: `CReal.converges_mul`
// -- already proved -- is used as a BLACK BOX to transport `F`'s own
// shared-mesh convergence through multiplication by the constant sequence
// `fun _ => c` (`CReal.converges_of_const`), rather than building a fresh
// bound on `CReal.mul` from `product::regular_between` directly. ----------

/// `CReal.integral_scale : ∀ c F a b hab uF ucF, Equiv (CReal.integral (fun
/// t => mul c (F t)) a b hab ucF) (mul c (CReal.integral F a b hab uF))`.
///
/// # The construction
///
/// 1. `combined := fun t => mul c (F t)`, EXACTLY [`declare_mul_riemann_sum`]'s
///    own `combined` builder, so every `rsum(combined, …)` built here
///    matches that theorem's LHS bit for bit.
/// 2. `f_lambda_f`/`integral_f_val`/`conv_f_native` (F's own native
///    [`integral_witness`]/[`CRealPrelude::integral_converges`]) and the
///    `combined` analogues `f_lambda_cf`/`integral_cf_val`/`conv_cf_native`.
/// 3. At a fresh accuracy index `n`: `m1 := deep(F,a,b,uF,n)+0`, `m2 :=
///    deep(combined,a,b,ucF,n)+0`, `l :=` [`common_refinement`]`(m1,m2)`'s
///    shared target -- EXACTLY [`declare_integral_le`]'s own `m1`/`m2`/`l`,
///    `combined` standing in for that declaration's `G`.
/// 4. Two [`CRealPrelude::riemann_sum_cauchy`] calls, the [`common_refinement`]
///    rewrite and [`CRealPrelude::shared_index_to_canonical`], folded via
///    [`bnd_leg_plus_share_le`] into a SHARED `natDivSucc(k,n)` -- verbatim
///    [`declare_integral_le`]'s own `app1`/`app2`/`cross_f_at_n`/
///    `cross_g_at_n` construction, `combined` in `G`'s slot
///    (`cross_cf_at_n` here).
/// 5. [`CRealPrelude::mul_riemann_sum`] applied at the SHARED `l`, then
///    applied at `n`: `Equiv`'s own `∀ n, Within(…)` unfolding gives `Within
///    (seq (rsum combined a b l) n − seq (mul c (rsum F a b l)) n)
///    (natDivSucc 2 n)` directly, no epsilon slack beyond `Equiv`'s own
///    fixed `2/(n+1)`.
/// 6. [`chain_within2`] combines step 5 (flipped) with `cross_cf_at_n` into
///    a single cross bound between `seq (mul c (rsum F a b l)) n` and
///    `combined`'s native sample `seq (rsum combined a b m2) n` (== `seq
///    (f_lambda_cf n) n` up to the beta [`integral_witness`]'s own `f_lambda`
///    reduces by), then [`CRealPrelude::converges_of_close`] transports
///    `conv_cf_native` across it to `Converges (fun n => mul c (rsum F a b
///    (l n))) integral_cf_val` (`step_cf`).
/// 7. [`CRealPrelude::converges_of_close`] ALSO transports `conv_f_native`
///    across the F-side leg from step 4 to `Converges (fun n => rsum F a b
///    (l n)) integral_f_val` (`step_f`, byte-identical in shape to
///    [`declare_integral_le`]'s own `step_f`).
/// 8. [`CRealPrelude::converges_mul`] at [`CRealPrelude::converges_of_const`]
///    `c` and `step_f` gives `Converges (fun n => mul c (rsum F a b (l n)))
///    (mul c integral_f_val)` -- the SAME sequence step 6 lands at, up to
///    the beta the kernel's own defeq check performs -- so
///    [`CRealPrelude::converges_unique`] closes `Equiv integral_cf_val (mul
///    c integral_f_val)` directly.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_integral_scale(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    // combined := fun t => mul c (F t) -- EXACTLY `mul_riemannSum`'s own
    // `combined` builder (`declare_mul_riemann_sum`), so every `rsum
    // (combined, …)` built here matches that theorem's LHS bit for bit.
    let combined = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let body = cmul(d, p, c, ft);
        d.lam_fv(t_fv, carrier, body)
    };

    let uf_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let uf_fv = d.fresh_fvar();
    let uf = d.kernel().fvar(uf_fv);
    let ucf_ty = d.const_app(p.uniformly_continuous_on, &[combined, a, b]);
    let ucf_fv = d.fresh_fvar();
    let ucf = d.kernel().fvar(ucf_fv);

    // --- native `integral_witness` triples. --------------------------------
    let (f_lambda_f, _kf_native, _cauchy_f) = integral_witness(d, p, f, a, b, hab, uf);
    let (f_lambda_cf, _kcf_native, _cauchy_cf) = integral_witness(d, p, combined, a, b, hab, ucf);

    let integral_f_val = d.const_app(p.integral, &[f, a, b, hab, uf]);
    let integral_cf_val = d.const_app(p.integral, &[combined, a, b, hab, ucf]);

    let conv_f_native = d.lemma(p.integral_converges, &[f, a, b, hab, uf]);
    let conv_cf_native = d.lemma(p.integral_converges, &[combined, a, b, hab, ucf]);

    let width = width_of(d, p, a, b);
    let (_c_bound, magnitude, _width_le_mag) = direct_bound_le(d, p, width);

    // --- the shared refinement `l(n)` and the two cross bounds, at a
    // symbolic accuracy index `n` -- verbatim `declare_integral_le`'s own
    // recipe, `combined` in `G`'s slot. -------------------------------------
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let deep_f_n = deep_at(d, p, f, a, b, uf, n);
    let zero1 = d.num(0);
    let m1 = NatOps::add(d, deep_f_n, zero1);
    let deep_cf_n = deep_at(d, p, combined, a, b, ucf, n);
    let zero2 = d.num(0);
    let m2 = NatOps::add(d, deep_cf_n, zero2);

    let h1 = d.lemma(p.riemann_sum_cauchy, &[f, a, b, n, m2, zero1, hab, uf]);
    let h2_raw = d.lemma(
        p.riemann_sum_cauchy,
        &[combined, a, b, n, m1, zero2, hab, ucf],
    );

    let (l, l2, l2_eq_l) = common_refinement(d, m1, m2);

    let h2 = {
        let rsum_m2_for_motive = rsum(d, p, combined, a, b, m2);
        let neg_rsum_m2_for_motive = cneg(d, p, rsum_m2_for_motive);
        nat_rewrite_prop(d, l2, l, l2_eq_l, h2_raw, &|d, x| {
            let rsum_x = rsum(d, p, combined, a, b, x);
            let t = cadd(d, p, rsum_x, neg_rsum_m2_for_motive);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let seq_t_i = sample(d, p, t, i);
            let bound_i = shared_accuracy_bound(d, p, a, b, n, m2, i);
            let claim = within(d, p, seq_t_i, bound_i);
            d.pi_fv(i_fv, nat, claim)
        })
    };

    let rsum_l_f = rsum(d, p, f, a, b, l);
    let rsum_m1 = rsum(d, p, f, a, b, m1);
    let rsum_l_cf = rsum(d, p, combined, a, b, l);
    let rsum_m2 = rsum(d, p, combined, a, b, m2);

    let bound1_fn = shared_accuracy_bound_fn(d, p, a, b, n, m1);
    let bound2_fn = shared_accuracy_bound_fn(d, p, a, b, n, m2);

    let app1 = d.lemma(
        p.shared_index_to_canonical,
        &[rsum_l_f, rsum_m1, bound1_fn, h1, n, n, n],
    );
    let app2 = d.lemma(
        p.shared_index_to_canonical,
        &[rsum_l_cf, rsum_m2, bound2_fn, h2, n, n, n],
    );

    let shift_n = shift(d, n);
    let m_n_sn = modulus(d, p, n, shift_n);
    let m_sn_n = modulus(d, p, shift_n, n);

    let bound1_n = d.apply(bound1_fn, &[n]);
    let bnd_a = {
        let inner = radd(d, m_n_sn, bound1_n);
        radd(d, inner, m_sn_n)
    };
    let bound2_n = d.apply(bound2_fn, &[n]);
    let bnd_c = {
        let inner = radd(d, m_n_sn, bound2_n);
        radd(d, inner, m_sn_n)
    };

    let (k, leg_f_extra_le) = bnd_leg_plus_share_le(d, p, a, b, n, m1, magnitude, bound1_n);
    let (_k_cf, leg_cf_extra_le) = bnd_leg_plus_share_le(d, p, a, b, n, m2, magnitude, bound2_n);
    let k_n = nds(d, p, k, n);

    let one_nat_f = d.num(1);
    let a1_n = div_succ(d, p, 1, n);
    let a1_nonneg_f = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat_f, n]);
    let bnd_a_le_extra = le_add_nonneg_right(d, p, bnd_a, a1_n, a1_nonneg_f);
    let bnd_a_extra = radd(d, bnd_a, a1_n);
    let bnd_a_le_k = d.lemma(
        p.rat.le_trans,
        &[bnd_a, bnd_a_extra, k_n, bnd_a_le_extra, leg_f_extra_le],
    );

    let one_nat_cf = d.num(1);
    let a1_n2 = div_succ(d, p, 1, n);
    let a1_nonneg_cf = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat_cf, n]);
    let bnd_c_le_extra = le_add_nonneg_right(d, p, bnd_c, a1_n2, a1_nonneg_cf);
    let bnd_c_extra = radd(d, bnd_c, a1_n2);
    let bnd_c_le_k = d.lemma(
        p.rat.le_trans,
        &[bnd_c, bnd_c_extra, k_n, bnd_c_le_extra, leg_cf_extra_le],
    );

    let seq_rsum_l_f_n = sample(d, p, rsum_l_f, n);
    let seq_rsum_m1_n = sample(d, p, rsum_m1, n);
    let diff_f = rsub(d, p.rat, seq_rsum_l_f_n, seq_rsum_m1_n);
    let cross_f_at_n = weaken(d, p, diff_f, bnd_a, k_n, app1, bnd_a_le_k);

    let seq_rsum_l_cf_n = sample(d, p, rsum_l_cf, n);
    let seq_rsum_m2_n = sample(d, p, rsum_m2, n);
    let diff_cf = rsub(d, p.rat, seq_rsum_l_cf_n, seq_rsum_m2_n);
    let cross_cf_at_n = weaken(d, p, diff_cf, bnd_c, k_n, app2, bnd_c_le_k);
    // cross_cf_at_n : Within (seq(rsum_l_cf) n - seq(rsum_m2) n) (natDivSucc k n)

    // --- step 5: `mul_riemannSum` at the SHARED `l`, applied at `n`. -------
    let mul_eq_l = d.lemma(p.mul_riemann_sum, &[c, f, a, b, l]);
    // mul_eq_l : Equiv (rsum combined a b l) (mul c (rsum f a b l))
    let mul_eq_n = d.apply(mul_eq_l, &[n]);
    // mul_eq_n : Within (seq(rsum_l_cf) n - seq(mul c rsum_l_f) n) (natDivSucc 2 n)

    let mul_c_rsum_l_f = cmul(d, p, c, rsum_l_f);
    let seq_mul_c_rsum_l_f_n = sample(d, p, mul_c_rsum_l_f, n);
    let two_n = div_succ(d, p, 2, n);
    let mul_eq_n_flip = within_symm(d, p, seq_rsum_l_cf_n, seq_mul_c_rsum_l_f_n, two_n, mul_eq_n);
    // mul_eq_n_flip : Within (seq(mul c rsum_l_f) n - seq(rsum_l_cf) n) (natDivSucc 2 n)

    // --- step 6: chain the flipped mul-leg with `cross_cf_at_n`, giving a
    // cross bound between `mul c (rsum F a b l)` and `combined`'s own
    // native mesh sample -- ready for `converges_of_close`. -----------------
    let cross_scale_raw = chain_within2(
        d,
        p,
        seq_mul_c_rsum_l_f_n,
        seq_rsum_l_cf_n,
        seq_rsum_m2_n,
        two_n,
        k_n,
        mul_eq_n_flip,
        cross_cf_at_n,
    );
    let two_lit = d.num(2);
    let (k2, k2_eq) = fuse_nds(d, p, two_lit, k, n);
    let k2_n = nds(d, p, k2, n);
    let cross_scale_bound = radd(d, two_n, k_n);
    let diff_scale = rsub(d, p.rat, seq_mul_c_rsum_l_f_n, seq_rsum_m2_n);
    let cross_scale = rat_eq_rewrite(
        d,
        cross_scale_bound,
        k2_n,
        k2_eq,
        cross_scale_raw,
        &|d, t| within(d, p, diff_scale, t),
    );

    // --- step 7: transport F's own native convergence to the shared mesh
    // (verbatim `declare_integral_le`'s own `step_f`). ----------------------
    let new_seq_f = d.lam_fv(n_fv, nat, rsum_l_f);
    let cross_f = d.lam_fv(n_fv, nat, cross_f_at_n);
    let step_f = d.lemma(
        p.converges_of_close,
        &[
            f_lambda_f,
            new_seq_f,
            integral_f_val,
            k,
            cross_f,
            conv_f_native,
        ],
    );
    // step_f : Converges new_seq_f integral_f_val

    // --- step 6, continued: transport `combined`'s own native convergence
    // across `cross_scale` to `Converges new_seq_cf integral_cf_val`,
    // `new_seq_cf(n) := mul c (rsum F a b (l n))`. --------------------------
    let new_seq_cf = d.lam_fv(n_fv, nat, mul_c_rsum_l_f);
    let cross_scale_lam = d.lam_fv(n_fv, nat, cross_scale);
    let step_cf = d.lemma(
        p.converges_of_close,
        &[
            f_lambda_cf,
            new_seq_cf,
            integral_cf_val,
            k2,
            cross_scale_lam,
            conv_cf_native,
        ],
    );
    // step_cf : Converges new_seq_cf integral_cf_val

    // --- step 8: `converges_mul` at the constant sequence, closing the gap
    // without touching `CReal.mul`'s own index-shift complexity by hand. ---
    let const_seq = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, nat, c)
    };
    let const_c = d.lemma(p.converges_of_const, &[c]);
    // const_c : Converges const_seq c
    let conv_scaled = d.lemma(
        p.converges_mul,
        &[const_seq, new_seq_f, c, integral_f_val, const_c, step_f],
    );
    // conv_scaled : Converges (fun n => mul (const_seq n) (new_seq_f n))
    //               (mul c integral_f_val) -- the SAME sequence `new_seq_cf`
    //               denotes, up to the two beta steps the kernel's own defeq
    //               check performs (`const_seq n ~> c`, `new_seq_f n ~>
    //               rsum_l_f`).

    let mul_c_integral_f_val = cmul(d, p, c, integral_f_val);
    let proof = d.lemma(
        p.converges_unique,
        &[
            new_seq_cf,
            integral_cf_val,
            mul_c_integral_f_val,
            step_cf,
            conv_scaled,
        ],
    );
    // proof : Equiv integral_cf_val (mul c integral_f_val)

    let concl = equiv(d, p, integral_cf_val, mul_c_integral_f_val);

    // `concl` mentions `hab`/`uF`/`ucF` (via `integral_f_val`/
    // `integral_cf_val`) and `c` (via `mul_c_integral_f_val`), so all four
    // must be bound with `pi_fv`, not `d.arrow` -- the same trap
    // `declare_integral_add`'s own doc comment names.
    let ty = {
        let after_ucf = d.pi_fv(ucf_fv, ucf_ty, concl);
        let after_uf = d.pi_fv(uf_fv, uf_ty, after_ucf);
        let after_hab = d.pi_fv(hab_fv, hab_ty, after_uf);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_f = d.pi_fv(f_fv, f_ty, over_a);
        d.pi_fv(c_fv, carrier, over_f)
    };
    let value = {
        let with_ucf = d.lam_fv(ucf_fv, ucf_ty, proof);
        let with_uf = d.lam_fv(uf_fv, uf_ty, with_ucf);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_uf);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_f = d.lam_fv(f_fv, f_ty, over_a);
        d.lam_fv(c_fv, carrier, over_f)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.integral_scale,
        uparams: vec![],
        ty,
        value,
    })
}

/// The Riemann-sum-vs-true-value estimate. See
/// [`CRealPrelude::riemann_sum_integral_close`] for the full statement.
///
/// **Measured 2026-08-27, and rebuilt because of it: routing leg 2 through
/// `speedup_close`/`kregular_of_cauchy_proof` (reconstructing
/// `integral_witness`'s triple to reach a NAMED rate) cost 74s of a 75s
/// prelude build, isolated by disabling each leg in turn and confirmed the
/// entire cost sat in leg 2 alone.** The mechanism: that route's `z :=
/// sample(integral_val, e)` (built directly from `CReal.integral`, a
/// `Definition` whose stored value embeds a full `regular_of_scaled_cauchy`
/// construction) has to be shown DEFEQ against a raw `speedup(raw,K) e`
/// term that never mentions `CReal.integral` at all -- the only way to
/// bridge them is a full delta-unfold of `CReal.integral`'s definition, and
/// that unfold is what was expensive. **Fixed by never triggering that
/// unfold**: leg 2 now goes through [`CRealPrelude::integral_converges`]
/// (an ALREADY-CHECKED fact) via [`exists_elim`], so the "z-side" bound
/// comes from ELIMINATING `Converges f_lambda integral_val`'s existential
/// rather than from re-deriving `speedup_close` by hand. The eliminated
/// witness's own type builds `integral_val` via the identical
/// `d.const_app(p.integral, ...)` recipe used here, so it is the SAME
/// `ExprId`, not merely defeq -- `CReal.integral`'s definition is never
/// unfolded at all. The rate `K` this needs is now genuinely NAMED (bound by
/// `exists_elim`'s own minor premise), just wrapped in an outer `∃ K` on the
/// final statement instead of hidden inside `Converges`'s wrapper -- a
/// single rate valid for every accuracy `e` (it depends only on `F`/`a`/`b`,
/// not on `e`), so it belongs OUTSIDE the `∀ e …` quantifiers rather than
/// threaded through them. Verified back to the ~18s prelude-build baseline
/// (`creal_prelude_builds`) after this change.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_integral_close(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    // `f_lambda` -- same recipe `integral_witness` uses, needed only to
    // STATE `integral_converges`'s own `Converges` predicate; the OTHER two
    // outputs of `integral_witness` (`K`, `cauchy_proof`) are not used --
    // see this function's own doc comment for why the `speedup_close` route
    // that DID use them was replaced.
    let (f_lambda, _kk_unused, _cauchy_unused) = integral_witness(d, p, f, a, b, hab, u);
    let integral_val = d.const_app(p.integral, &[f, a, b, hab, u]);

    let converges_fact = d.lemma(p.integral_converges, &[f, a, b, hab, u]);
    let predicate = converges_predicate(d, p, f_lambda, integral_val);

    // `k_fv`/`h_fv`: the eliminated witness/proof of `Converges f_lambda
    // integral_val` -- in scope for the whole `minor` body below, bound by
    // `exists_elim` itself (via `minor`'s own two lambdas), not by an outer
    // `pi_fv` on this declaration's own type.
    let k_fv = d.fresh_fvar();
    let kk = d.kernel().fvar(k_fv);
    let h_fv = d.fresh_fvar();
    let hh = d.kernel().fvar(h_fv);
    let hh_ty = d.apply(predicate, &[kk]);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let depth_fv = d.fresh_fvar();
    let depth = d.kernel().fvar(depth_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let jj1_fv = d.fresh_fvar();
    let jj1 = d.kernel().fvar(jj1_fv);
    let jj2_fv = d.fresh_fvar();
    let jj2 = d.kernel().fvar(jj2_fv);

    // m1 := deep(e) + depth -- the FIXED, arbitrary-depth mesh this estimate
    // is about. m2 := deep(e) + 0, EXACTLY `integral_witness`'s own
    // `f_lambda` evaluated at `e` (same `deep_at`/`NatOps::add`/`d.num(0)`
    // recipe -- see that function's own body).
    let deep = deep_at(d, p, f, a, b, u, e);
    let zero_nat = d.num(0);
    let m1 = NatOps::add(d, deep, depth);
    let m2 = NatOps::add(d, deep, zero_nat);

    // --- Leg 1: fixed mesh `m1` vs `m2` (= `f_lambda e`), at
    // (oi, oj, jj1, jj2) := (i, e, jj1, jj2). --------------------------------
    let leg1 = d.lemma(
        p.riemann_sum_shared_accuracy_close,
        &[f, a, b, e, depth, zero_nat, hab, u, i, e, jj1, jj2],
    );

    // Reconstruct `riemann_sum_shared_accuracy_close`'s own final bound
    // EXTERNALLY, term-for-term (SAME `common_refinement`/
    // `shared_accuracy_bound_fn` recipe at the SAME `m1`/`m2`), so `bound_leg1`
    // is the SAME `ExprId` its own conclusion carries -- the same
    // reconstruction discipline `total_eps_of`'s own doc comment explains.
    // (Confirmed CHEAP in isolation: this leg alone costs no more than the
    // ~18s baseline -- the expensive leg was leg 2, above.)
    let (l, _l2, _l2_eq_l) = common_refinement(d, m1, m2);
    let shift_jj1 = shift(d, jj1);
    let shift_jj2 = shift(d, jj2);
    let bound1_fn = shared_accuracy_bound_fn(d, p, a, b, e, m1);
    let bound2_fn = shared_accuracy_bound_fn(d, p, a, b, e, m2);
    let bound1_jj1 = d.apply(bound1_fn, &[jj1]);
    let bound2_jj2 = d.apply(bound2_fn, &[jj2]);
    let m_l_sj1 = modulus(d, p, l, shift_jj1);
    let m_sj1_i = modulus(d, p, shift_jj1, i);
    let m_l_sj2 = modulus(d, p, l, shift_jj2);
    let m_sj2_e = modulus(d, p, shift_jj2, e);
    let m_l_sj1_plus_bound1 = radd(d, m_l_sj1, bound1_jj1);
    let bnd1 = radd(d, m_l_sj1_plus_bound1, m_sj1_i);
    let m_l_sj2_plus_bound2 = radd(d, m_l_sj2, bound2_jj2);
    let bnd2 = radd(d, m_l_sj2_plus_bound2, m_sj2_e);
    let bound_leg1 = radd(d, bnd1, bnd2);

    let rsum_m1 = rsum(d, p, f, a, b, m1);
    let rsum_m2 = rsum(d, p, f, a, b, m2);
    let x = sample(d, p, rsum_m1, i);
    let y = sample(d, p, rsum_m2, e);

    // --- Leg 2: `hh` applied at `e` -- EXACTLY `converges_predicate`'s own
    // per-index bound at (kk, e): `Within(sample(f_lambda e, e) -
    // sample(integral_val, e))(natDivSucc kk e)`. `f_lambda e` beta-reduces
    // (pure substitution on a LOCAL lambda -- no Definition unfold) to
    // `rsum_m2`'s own sample at `e` (`y`, above); `integral_val` is the
    // SAME `ExprId` on both sides. Neither side ever needs
    // `CReal.integral`'s definition unfolded. -------------------------------
    let leg2 = d.apply(hh, &[e]);
    let bound_leg2 = div_succ_at(d, p, kk, e);

    let z = sample(d, p, integral_val, e);

    let final_proof_inner = chain_within2(d, p, x, y, z, bound_leg1, bound_leg2, leg1, leg2);
    let final_bound = radd(d, bound_leg1, bound_leg2);

    let diff = rsub(d, p.rat, x, z);
    let concl_ty = within(d, p, diff, final_bound);

    // per-K statement: `∀ e depth i j1 j2, Within(diff)(final_bound(K))`.
    let per_k_ty = {
        let after_jj2 = d.pi_fv(jj2_fv, nat, concl_ty);
        let after_jj1 = d.pi_fv(jj1_fv, nat, after_jj2);
        let after_i = d.pi_fv(i_fv, nat, after_jj1);
        let after_depth = d.pi_fv(depth_fv, nat, after_i);
        d.pi_fv(e_fv, nat, after_depth)
    };
    let per_k_value = {
        let with_jj2 = d.lam_fv(jj2_fv, nat, final_proof_inner);
        let with_jj1 = d.lam_fv(jj1_fv, nat, with_jj2);
        let with_i = d.lam_fv(i_fv, nat, with_jj1);
        let with_depth = d.lam_fv(depth_fv, nat, with_i);
        d.lam_fv(e_fv, nat, with_depth)
    };

    // outer_predicate(K) := `∀ e depth i j1 j2, Within(diff)(final_bound(K))`,
    // as an actual `Nat -> Prop` term, for `exists_ty`'s own `predicate`
    // argument.
    let outer_predicate = d.lam_fv(k_fv, nat, per_k_ty);
    let target_ty = exists_ty(d, p, nat, outer_predicate);

    // `minor : ∀ K, (predicate K) -> target_ty`, `predicate` here being
    // `Converges f_lambda integral_val`'s own per-`K` body (`hh_ty`'s own
    // binder) -- built as `Exists.intro` at witness `kk`, using `hh`
    // (bound by this SAME `minor`) to build `leg2` above.
    let target_witness_proof = exists_intro(d, p, nat, outer_predicate, kk, per_k_value);
    let minor = {
        let with_h = d.lam_fv(h_fv, hh_ty, target_witness_proof);
        d.lam_fv(k_fv, nat, with_h)
    };

    let full_proof = exists_elim(d, predicate, target_ty, converges_fact, minor);

    // `target_ty` mentions `hab`/`u` (via `integral_val`, inside `z`/`diff`
    // inside `per_k_ty`), so both must be bound with `pi_fv`, not
    // `d.arrow` -- the identical trap `declare_integral_const`'s own doc
    // comment names.
    let ty = {
        let after_u = d.pi_fv(u_fv, u_ty, target_ty);
        let after_hab = d.pi_fv(hab_fv, hab_ty, after_u);
        let over_b = d.pi_fv(b_fv, carrier, after_hab);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_u = d.lam_fv(u_fv, u_ty, full_proof);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_b = d.lam_fv(b_fv, carrier, with_hab);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_integral_close,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.close_within_of_within_indexed` -- the `Within` -> `CReal.le
// (abs …)` bridge at TWO INDEPENDENT sample indices --------------------------
//
// `uniform_convergence.rs`'s `CReal.close_within_of_within` already bridges a
// raw rational `Within` bound to a genuine `CReal.le (abs …)` fact, but its
// own hypothesis is `Within (sub (sample x n) (sample y n)) (natDivSucc k n)`
// -- BOTH sides sampled at the SAME index `n`. `riemannSum_integral_close`'s
// own conclusion compares `riemannSum`'s sample at an arbitrary `i` against
// `integral`'s sample at the accuracy index `e`: two indices that are never
// tied by a common denominator anywhere upstream, and cannot be forced equal
// (`i` ranges over every mesh-refinement/crossing index the Riemann-sum side
// needs; `e` is fixed by the caller's target accuracy). This section
// generalizes the bridge to that shape.
//
// Route: identical algebra to `one_sided_via_samples`
// (`uniform_convergence.rs`, itself private to that module -- Rust privacy,
// sibling module), run ONCE per direction with each side's OWN
// `1/(index+1)`-slack self-approximation
// (`CRealPrelude::sample_upper_bound`/`sample_lower_bound`) read at ITS OWN
// index rather than a shared one. Because the two directions apply that
// asymmetric recipe with `(i, e)` in opposite roles, they land on
// `Rat.add (natDivSucc 1 e) (Rat.add q (natDivSucc 1 i))` and `Rat.add
// (natDivSucc 1 i) (Rat.add q (natDivSucc 1 e))` respectively -- equal only up
// to `Rat.add_assoc`/`Rat.add_comm`, never syntactically -- so [`reassoc3`]
// closes each to one shared target before `CRealPrelude::abs_le_of_two_sided`
// can fire on them together.

/// `Rat.Eq (Rat.add (Rat.sub a b) b) a` — adding back what was subtracted
/// cancels, at `Rat`. A private copy of the technique
/// `uniform_convergence.rs`'s own (unexported) `sub_add_cancel` uses (Rust
/// privacy: sibling module), needed by [`one_sided_two_index`] in the same
/// role.
fn rat_sub_add_cancel(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let rat = p.rat;
    let neg_b = rneg(d, b);
    let a_negb = radd(d, a, neg_b);
    let lhs = radd(d, a_negb, b);
    let assoc = d.lemma(rat.add_assoc, &[a, neg_b, b]);
    // assoc : Eq lhs (add a (add neg_b b))
    let negb_b = radd(d, neg_b, b);
    let cancel_inner = d.lemma(rat.neg_add_cancel, &[b]); // Eq negb_b zero
    let zero = rzero(d, rat);
    let cancel = rcongr(d, negb_b, zero, cancel_inner, &|d, t| radd(d, a, t));
    let a_plus_zero = radd(d, a, zero);
    let add_zero_proof = d.lemma(rat.add_zero, &[a]); // Eq a_plus_zero a
    let a_radd_negb_b = radd(d, a, negb_b);
    let (_, proof) = rchain(
        d,
        lhs,
        &[
            (a_radd_negb_b, assoc),
            (a_plus_zero, cancel),
            (a, add_zero_proof),
        ],
    );
    proof
}

/// `Rat.Eq (Rat.add a (Rat.add b c)) (Rat.add b (Rat.add c a))` — the
/// three-atom commute-and-reassociate [`close_of_within_indexed`] needs to
/// unify its two directions' bounds (built by the SAME asymmetric recipe with
/// two of the three atoms swapped) onto one shared target, via
/// `Rat.add_assoc`(symm)/`Rat.add_comm`/`Rat.add_assoc`/`Rat.add_comm` in that
/// order — the same shape of atom-shuffle [`mesh_scale_by_succ_k`] uses
/// (below), here on three atoms rather than four.
///
/// Returns `(target, proof)` where `target := Rat.add b (Rat.add c a)`.
fn reassoc3(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let bc = radd(d, b, c);
    let source = radd(d, a, bc);

    let ab = radd(d, a, b);
    let target1 = radd(d, ab, c);
    let assoc1 = d.lemma(rat.add_assoc, &[a, b, c]); // Eq target1 source
    let eq1 = rsymm(d, target1, source, assoc1); // Eq source target1

    let ba = radd(d, b, a);
    let target2 = radd(d, ba, c);
    let comm1 = d.lemma(rat.add_comm, &[a, b]); // Eq ab ba
    let eq2 = rcongr(d, ab, ba, comm1, &|d, t| radd(d, t, c)); // Eq target1 target2

    let ac = radd(d, a, c);
    let target3 = radd(d, b, ac);
    let eq3 = d.lemma(rat.add_assoc, &[b, a, c]); // Eq target2 target3

    let ca = radd(d, c, a);
    let target4 = radd(d, b, ca);
    let comm2 = d.lemma(rat.add_comm, &[a, c]); // Eq ac ca
    let eq4 = rcongr(d, ac, ca, comm2, &|d, t| radd(d, b, t)); // Eq target3 target4

    let (_, proof) = rchain(
        d,
        source,
        &[
            (target1, eq1),
            (target2, eq2),
            (target3, eq3),
            (target4, eq4),
        ],
    );
    (target4, proof)
}

/// The two-independent-index generalization of `uniform_convergence.rs`'s
/// own (unexported) `one_sided_via_samples`: from `upper_uv : Rat.le (rsub
/// (sample u n_u) (sample v n_v)) bk`, derive `(bound, proof)` where `bound
/// := Rat.add o_v (Rat.add bk o_u)` (`o_u := natDivSucc 1 n_u`, `o_v :=
/// natDivSucc 1 n_v`) and `proof : CReal.le u (CReal.add v (CReal.ofRat
/// bound))`.
///
/// Identical algebra to the shared-index original — `u`'s own
/// `1/(n_u+1)`-slack self-approximation ([`CRealPrelude::sample_upper_bound`]
/// at `n_u`) chains through `upper_uv` into `v`'s OWN sample at `n_v`; `v`'s
/// sample is then rewritten as `(sample(v,n_v) - o_v) + o_v` so `v`'s own
/// `1/(n_v+1)`-slack self-approximation ([`CRealPrelude::sample_lower_bound`]
/// at `n_v`) applies directly — with `n_u`/`n_v` genuinely independent
/// throughout (never assumed equal, never compared to each other).
fn one_sided_two_index(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    n_u: ExprId,
    n_v: ExprId,
    bk: ExprId,
    upper_uv: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let o_u = div_succ_at(d, p, one_nat, n_u);
    let o_v = div_succ_at(d, p, one_nat, n_v);

    let au = sample(d, p, u, n_u);
    let av = sample(d, p, v, n_v);

    // au_le_avbk : Rat.le au (Rat.add av bk).
    let au_le_avbk = d.lemma(rat.le_of_sub_le, &[au, av, bk, upper_uv]);

    // step2 : Rat.le (au+o_u) ((av+bk)+o_u).
    let o_u_refl = d.lemma(rat.le_refl, &[o_u]);
    let av_bk = radd(d, av, bk);
    let step2 = d.lemma(rat.add_le_add, &[au, av_bk, o_u, o_u, au_le_avbk, o_u_refl]);

    // step3 : Rat.le (au+o_u) (av+(bk+o_u)).
    let bk_ou = radd(d, bk, o_u);
    let av_bk_ou = radd(d, av, bk_ou);
    let assoc1 = d.lemma(rat.add_assoc, &[av, bk, o_u]);
    let au_ou = radd(d, au, o_u);
    let av_bk_then_ou = radd(d, av_bk, o_u);
    let step3 = rat_eq_rewrite(d, av_bk_then_ou, av_bk_ou, assoc1, step2, &|d, t| {
        rle(d, rat, au_ou, t)
    });

    // bridge_eq : Eq (av+bk_ou) ((av-o_v)+(o_v+bk_ou)).
    let av_minus_ov = rsub(d, rat, av, o_v);
    let cancel = rat_sub_add_cancel(d, p, av, o_v); // Eq (radd av_minus_ov o_v) av
    let restored = radd(d, av_minus_ov, o_v);
    let cancel_symm = rsymm(d, restored, av, cancel); // Eq av restored
    let av_bko_congr = rcongr(d, av, restored, cancel_symm, &|d, t| radd(d, t, bk_ou));
    let o_v_bk_ou = radd(d, o_v, bk_ou);
    let assoc2 = d.lemma(rat.add_assoc, &[av_minus_ov, o_v, bk_ou]);
    let target_shape = radd(d, av_minus_ov, o_v_bk_ou);
    let restored_bk_ou = radd(d, restored, bk_ou);
    let (_, bridge_eq) = rchain(
        d,
        av_bk_ou,
        &[(restored_bk_ou, av_bko_congr), (target_shape, assoc2)],
    );

    // step4 : Rat.le (au+o_u) ((av-o_v)+(o_v+bk_ou)).
    let step4 = rat_eq_rewrite(d, av_bk_ou, target_shape, bridge_eq, step3, &|d, t| {
        rle(d, rat, au_ou, t)
    });

    // chain1 : CReal.le u (ofRat target_shape).
    let hu_upper = d.lemma(p.sample_upper_bound, &[u, n_u]);
    let mid = embed(d, p, au_ou);
    let target1 = embed(d, p, target_shape);
    let ofrat_le_1 = d.lemma(p.of_rat_le, &[au_ou, target_shape, step4]);
    let chain1 = d.lemma(p.le_trans, &[u, mid, target1, hu_upper, ofrat_le_1]);

    // chain2 : CReal.le u (add (ofRat av_minus_ov) (ofRat o_v_bk_ou)), splitting
    // `target1` via `CReal.ofRat_add`.
    let embed_av_minus_ov = embed(d, p, av_minus_ov);
    let embed_o_v_bk_ou = embed(d, p, o_v_bk_ou);
    let split = d.const_app(p.add, &[embed_av_minus_ov, embed_o_v_bk_ou]);
    let fuse = d.lemma(p.of_rat_add, &[av_minus_ov, o_v_bk_ou]);
    // fuse : Equiv split target1
    let fuse_symm = d.lemma(p.equiv_symm, &[split, target1, fuse]);
    let refl_u = d.lemma(p.equiv_refl, &[u]);
    let chain2 = d.lemma(
        p.le_congr,
        &[u, u, target1, split, refl_u, fuse_symm, chain1],
    );

    // step5 : CReal.le split (add v (ofRat o_v_bk_ou)), via `sample_lower_bound`.
    let hv_lower = d.lemma(p.sample_lower_bound, &[v, n_v]);
    let o_v_bk_ou_refl = d.lemma(p.le_refl, &[embed_o_v_bk_ou]);
    let step5 = d.lemma(
        p.add_le_add,
        &[
            embed_av_minus_ov,
            v,
            embed_o_v_bk_ou,
            embed_o_v_bk_ou,
            hv_lower,
            o_v_bk_ou_refl,
        ],
    );

    let final_target = d.const_app(p.add, &[v, embed_o_v_bk_ou]);
    let result = d.lemma(p.le_trans, &[u, split, final_target, chain2, step5]);
    (o_v_bk_ou, result)
}

/// From `hp : Within (Rat.sub (sample x i) (sample y e)) q`, derive `(bound,
/// proof)` where `bound := Rat.add q (Rat.add (natDivSucc 1 i) (natDivSucc 1
/// e))` and `proof : CReal.le (CReal.abs (CReal.add x (CReal.neg y)))
/// (CReal.ofRat bound)` — the `Within` → `CReal.le (abs …)` bridge at two
/// INDEPENDENT sample indices. See this section's own module documentation
/// (just above [`rat_sub_add_cancel`]) for the route and why
/// `close_within_of_within`'s shared-index version does not cover
/// `riemannSum_integral_close`'s own shape.
fn close_of_within_indexed(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    i: ExprId,
    e: ExprId,
    q: ExprId,
    hp: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let ax = sample(d, p, x, i);
    let ay = sample(d, p, y, e);
    let diff = rsub(d, rat, ax, ay);
    let (hp_lower, hp_upper) = halves(d, p, diff, q, hp);

    // hp_upper_swapped : Rat.le (sub ay ax) q.
    let hp_upper_swapped = {
        let neg_q = rneg(d, q);
        let neg_diff = rneg(d, diff);
        let bn_left = rle(d, rat, neg_q, neg_diff);
        let bn_right = rle(d, rat, neg_diff, q);
        let bn = d.lemma(rat.bounds_neg, &[diff, q, hp_lower, hp_upper]);
        let raw = d.and_right(bn_left, bn_right, bn);
        let ay_ax = rsub(d, rat, ay, ax);
        let neg_sub_eq = d.lemma(rat.neg_sub, &[ax, ay]); // Eq neg_diff ay_ax
        rat_eq_rewrite(d, neg_diff, ay_ax, neg_sub_eq, raw, &|d, t| {
            rle(d, rat, t, q)
        })
    };

    let (bound1, goal_up) = one_sided_two_index(d, p, x, y, i, e, q, hp_upper);
    let (bound2, goal_down) = one_sided_two_index(d, p, y, x, e, i, q, hp_upper_swapped);

    let one_nat = d.num(1);
    let o_i = div_succ_at(d, p, one_nat, i);
    let o_e = div_succ_at(d, p, one_nat, e);

    // bound1 = o_e + (q + o_i); reassoc3(o_e, q, o_i) lands on q + (o_i + o_e).
    let (target, eq_bound1_target) = reassoc3(d, p, o_e, q, o_i);
    // bound2 = o_i + (q + o_e); reassoc3(o_i, q, o_e) lands on q + (o_e + o_i),
    // one more `add_comm` away from `target`.
    let (mid_target, eq_bound2_mid) = reassoc3(d, p, o_i, q, o_e);
    let eq_bound2_target = {
        let oi_oe = radd(d, o_i, o_e);
        let oe_oi = radd(d, o_e, o_i);
        let comm = d.lemma(rat.add_comm, &[o_e, o_i]); // Eq oe_oi oi_oe
        let congr_final = rcongr(d, oe_oi, oi_oe, comm, &|d, t| radd(d, q, t));
        // congr_final : Eq mid_target target
        let (_, chained) = rchain(
            d,
            bound2,
            &[(mid_target, eq_bound2_mid), (target, congr_final)],
        );
        chained
    };

    let goal_up_t = rat_eq_rewrite(d, bound1, target, eq_bound1_target, goal_up, &|d, t| {
        let et = embed(d, p, t);
        let rhs = cadd(d, p, y, et);
        cle(d, p, x, rhs)
    });
    let goal_down_t = rat_eq_rewrite(d, bound2, target, eq_bound2_target, goal_down, &|d, t| {
        let et = embed(d, p, t);
        let rhs = cadd(d, p, x, et);
        cle(d, p, y, rhs)
    });

    let proof = d.lemma(
        p.abs_le_of_two_sided,
        &[x, y, target, goal_up_t, goal_down_t],
    );
    (target, proof)
}

/// Admit `CReal.close_within_of_within_indexed`. See this section's own
/// module documentation for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// refused a proof, not that a script gave up.
pub(super) fn declare_close_within_of_within_indexed(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rat_carrier = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let ax = sample(d, p, x, i);
    let ay = sample(d, p, y, e);
    let diff = rsub(d, p.rat, ax, ay);
    let hyp_ty = within(d, p, diff, q);
    let hp_fv = d.fresh_fvar();
    let hp = d.kernel().fvar(hp_fv);

    let (bound, proof) = close_of_within_indexed(d, p, x, y, i, e, q, hp);

    let ny = cneg(d, p, y);
    let diff_xy = cadd(d, p, x, ny);
    let mag = d.const_app(p.abs, &[diff_xy]);
    let embedded_bound = embed(d, p, bound);
    let concl_ty = cle(d, p, mag, embedded_bound);

    let ty = {
        let inner = d.arrow(hyp_ty, concl_ty);
        let with_q = d.pi_fv(q_fv, rat_carrier, inner);
        let with_e = d.pi_fv(e_fv, nat, with_q);
        let with_i = d.pi_fv(i_fv, nat, with_e);
        let with_y = d.pi_fv(y_fv, carrier, with_i);
        d.pi_fv(x_fv, carrier, with_y)
    };
    let value = {
        let with_hp = d.lam_fv(hp_fv, hyp_ty, proof);
        let with_q = d.lam_fv(q_fv, rat_carrier, with_hp);
        let with_e = d.lam_fv(e_fv, nat, with_q);
        let with_i = d.lam_fv(i_fv, nat, with_e);
        let with_y = d.lam_fv(y_fv, carrier, with_i);
        d.lam_fv(x_fv, carrier, with_y)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.close_within_of_within_indexed,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.riemannSum_split_exact` -- the NINTH `integral_split` slice:
// exact index-algebra interval split at a RATIONAL-PROPORTION split point.
// See this module's own ninth `integral_split` documentation entry for the
// full argument. Summary: choosing `c` to BE the `(succ m_ac)`-th sample
// point of a refined `[a,b]` mesh (rather than an arbitrary `CReal`) makes
// the two sub-interval mesh widths EXACT algebraic multiples of the parent
// mesh's own width -- no crossing index, no uniform-continuity estimate, no
// `CReal.inv` -- and the whole split collapses to `CReal.sumRange_split`
// plus this section's arithmetic. The one genuinely new hypothesis is `F`
// respecting `Equiv` (`hcong` below): riemannSum's summand samples `F` at
// two POINTS that are only `Equiv`, never definitionally equal, once the
// mesh is refined, and nothing about an arbitrary `F : CReal -> CReal`
// forces that on its own.

/// `Rat.natDivSucc 1 m`, embedded into `CReal` -- the mesh reciprocal
/// [`delta_of`] builds internally, exposed here so callers relating it via
/// [`CRealPrelude::mesh_count_width`] do not have to guess `delta_of`'s exact
/// recipe. Built with the identical `d.num`/`const_app`/`embed` calls
/// `delta_of` uses, so the two calls intern to the SAME `ExprId`.
fn frac_of(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    embed(d, p, frac)
}

/// `Equiv (width_of x (add x w)) w` -- cancelling a shift back out of its own
/// endpoint's width: `(x + w) - x ~ w`. `add_comm`/`add_assoc`/`add_neg`/
/// `add_zero`, the same shape used everywhere a sample point is peeled back
/// to its offset.
fn cancel_width(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, w: ExprId) -> ExprId {
    let y = cadd(d, p, x, w);
    let start = width_of(d, p, x, y); // add y (neg x) = add (add x w) (neg x)
    let nx = cneg(d, p, x);

    let xw = cadd(d, p, x, w);
    let wx = cadd(d, p, w, x);
    let mid1 = cadd(d, p, wx, nx);
    let comm1 = d.lemma(p.add_comm, &[x, w]); // Equiv xw wx
    let refl_nx = d.lemma(p.equiv_refl, &[nx]);
    let step1 = d.lemma(p.add_congr, &[xw, wx, nx, nx, comm1, refl_nx]); // Equiv start mid1

    let xnx = cadd(d, p, x, nx);
    let mid2 = cadd(d, p, w, xnx);
    let step2 = d.lemma(p.add_assoc, &[w, x, nx]); // Equiv mid1 mid2

    let zero_c = czero(d, p);
    let an = d.lemma(p.add_neg, &[x]); // Equiv xnx zero
    let refl_w = d.lemma(p.equiv_refl, &[w]);
    let w_zero = cadd(d, p, w, zero_c);
    let step3 = d.lemma(p.add_congr, &[w, w, xnx, zero_c, refl_w, an]); // Equiv mid2 w_zero
    let step4 = d.lemma(p.add_zero, &[w]); // Equiv w_zero w

    echain(
        d,
        p,
        start,
        &[(mid1, step1), (mid2, step2), (w_zero, step3), (w, step4)],
    )
}

/// `Equiv y (add x (width_of x y))` -- the reverse of [`cancel_width`]:
/// uncancelling a width back into a sum. `y ~ y+0 ~ y+((-x)+x) ~
/// (y+(-x))+x = width_of(x,y)+x ~ x+width_of(x,y)`.
fn uncancel_width(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let width = width_of(d, p, x, y); // add y (neg x)
    let nx = cneg(d, p, x);
    let zero_c = czero(d, p);

    let y_zero = cadd(d, p, y, zero_c);
    let az_y = d.lemma(p.add_zero, &[y]); // Equiv y_zero y
    let flip0 = d.lemma(p.equiv_symm, &[y_zero, y, az_y]); // Equiv y y_zero

    let xnx = cadd(d, p, x, nx);
    let nxx = cadd(d, p, nx, x);
    let comm_nx = d.lemma(p.add_comm, &[nx, x]); // Equiv nxx xnx
    let an = d.lemma(p.add_neg, &[x]); // Equiv xnx zero
    let nxx_zero = d.lemma(p.equiv_trans, &[nxx, xnx, zero_c, comm_nx, an]); // Equiv nxx zero
    let flip1 = d.lemma(p.equiv_symm, &[nxx, zero_c, nxx_zero]); // Equiv zero nxx

    let refl_y = d.lemma(p.equiv_refl, &[y]);
    let y_nxx = cadd(d, p, y, nxx);
    let step1 = d.lemma(p.add_congr, &[y, y, zero_c, nxx, refl_y, flip1]); // Equiv y_zero y_nxx

    let width_x = cadd(d, p, width, x); // add (add y nx) x
    let assoc = d.lemma(p.add_assoc, &[y, nx, x]); // Equiv width_x y_nxx
    let step2 = d.lemma(p.equiv_symm, &[width_x, y_nxx, assoc]); // Equiv y_nxx width_x

    let x_width = cadd(d, p, x, width);
    let comm_final = d.lemma(p.add_comm, &[width, x]); // Equiv width_x x_width

    echain(
        d,
        p,
        y,
        &[
            (y_zero, flip0),
            (y_nxx, step1),
            (width_x, step2),
            (x_width, comm_final),
        ],
    )
}

/// Given `h_width : Equiv width_actual w` where `w := mul on delta_ref`
/// (`on := ofNat n`, `n := succ m`), and `delta_actual := mul width_actual
/// (frac_of m)`, returns `Equiv delta_actual delta_ref` --
/// [`CRealPrelude::mesh_count_width`] read backwards: once the OTHER
/// interval's own width agrees with `w`, refining it by `m` reproduces
/// `delta_ref` exactly.
#[allow(clippy::too_many_arguments)]
fn delta_from_width_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    width_actual: ExprId,
    h_width: ExprId,
    w: ExprId,
    delta_ref: ExprId,
    on: ExprId,
    frac: ExprId,
    delta_actual: ExprId,
    m: ExprId,
) -> ExprId {
    let mul_w_frac = cmul(d, p, w, frac);
    let refl_frac = d.lemma(p.equiv_refl, &[frac]);
    let step_a = d.lemma(
        p.mul_congr,
        &[width_actual, w, frac, frac, h_width, refl_frac],
    ); // Equiv delta_actual mul_w_frac

    let inner = cmul(d, p, delta_ref, frac);
    let mid = cmul(d, p, on, inner);
    let step_b = d.lemma(p.mul_assoc, &[on, delta_ref, frac]); // Equiv mul_w_frac mid

    let step_c = d.lemma(p.mesh_count_width, &[delta_ref, m]); // Equiv mid delta_ref

    echain(
        d,
        p,
        delta_actual,
        &[(mul_w_frac, step_a), (mid, step_b), (delta_ref, step_c)],
    )
}

/// `fun k => f (add m k)` -- structurally identical to
/// `series.rs`'/`geometric.rs`'s own private `shifted_fn` recipe (same
/// `NatOps::add` + `apply` + `lam_fv` shape), rebuilt here since neither is
/// visible outside its own module; interning makes this call and
/// [`CRealPrelude::sum_range_split`]'s own internal use of the identical
/// shape produce the SAME `ExprId`.
fn shifted_fn(d: &mut IntDev<'_>, m: ExprId, f: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let mk = NatOps::add(d, m, k);
    let body = d.apply(f, &[mk]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// Admit `CReal.riemannSum_split_exact : ∀ F a b m_ac m_cb, (∀ x y, Equiv x y
/// -> Equiv (F x) (F y)) -> Equiv (riemannSum F a b (add (Nat.succ m_ac)
/// m_cb)) (add (riemannSum F a c m_ac) (riemannSum F c b m_cb))`, `c := add a
/// (mul (ofNat (Nat.succ m_ac)) (delta_of a b (add (Nat.succ m_ac) m_cb)))` --
/// `c` IS the `(succ m_ac)`-th sample point of the refined `[a,b]` mesh.
///
/// See this module's ninth `integral_split` documentation entry for the full
/// derivation this mirrors: `H_split` (the parent mesh's width is EXACTLY the
/// sum of the two sub-widths, via [`CRealPrelude::of_nat_add`] +
/// [`right_distrib`] + [`CRealPrelude::mesh_count_width`]), `H_b`/`H_cb`
/// (uncancelling/cancelling that width equation to place `c` between `a` and
/// `b`), the two `delta_from_width_equiv` calls (the sub-interval mesh steps
/// EQUAL the parent's, not merely close), and finally
/// [`CRealPrelude::sum_range_split`] plus two [`CRealPrelude::sum_range_congr`]
/// calls (using `hcong` to move between `Equiv`-related sample points) to
/// glue the split sum back into the two child `riemannSum`s.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_split_exact(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let mac_fv = d.fresh_fvar();
    let m_ac = d.kernel().fvar(mac_fv);
    let mcb_fv = d.fresh_fvar();
    let m_cb = d.kernel().fvar(mcb_fv);

    let hcong_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hxy_ty = equiv(d, p, x, y);
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let concl = equiv(d, p, fx, fy);
        let arrow_ty = d.arrow(hxy_ty, concl);
        let over_y = d.pi_fv(y_fv, carrier, arrow_ty);
        d.pi_fv(x_fv, carrier, over_y)
    };
    let hcong_fv = d.fresh_fvar();
    let hcong = d.kernel().fvar(hcong_fv);

    let n_ac = d.succ(m_ac);
    let n_cb = d.succ(m_cb);
    let m_ab = NatOps::add(d, n_ac, m_cb);

    let delta_ab = delta_of(d, p, a, b, m_ab);
    let width_ab = width_of(d, p, a, b);

    let on_ac = d.const_app(p.of_nat, &[n_ac]);
    let on_cb = d.const_app(p.of_nat, &[n_cb]);
    let w1 = cmul(d, p, on_ac, delta_ab);
    let w2 = cmul(d, p, on_cb, delta_ab);
    let c = cadd(d, p, a, w1);

    // --- H_split : Equiv width_ab (add w1 w2) ---
    let h_split = {
        let mcw_ab = d.lemma(p.mesh_count_width, &[width_ab, m_ab]);
        let sm_ab = d.succ(m_ab);
        let on_sm_ab = d.const_app(p.of_nat, &[sm_ab]);
        let mid0 = cmul(d, p, on_sm_ab, delta_ab);
        let hw_ab = d.lemma(p.equiv_symm, &[mid0, width_ab, mcw_ab]);

        let h_ofnat_split = d.lemma(p.of_nat_add, &[n_ac, n_cb]);
        let sum_on = cadd(d, p, on_ac, on_cb);
        let mid1 = cmul(d, p, sum_on, delta_ab);
        let refl_delta_ab = d.lemma(p.equiv_refl, &[delta_ab]);
        let step_a = d.lemma(
            p.mul_congr,
            &[
                on_sm_ab,
                sum_on,
                delta_ab,
                delta_ab,
                h_ofnat_split,
                refl_delta_ab,
            ],
        );

        let add_w1w2 = cadd(d, p, w1, w2);
        let step_b = right_distrib(d, p, on_ac, on_cb, delta_ab);

        echain(
            d,
            p,
            width_ab,
            &[(mid0, hw_ab), (mid1, step_a), (add_w1w2, step_b)],
        )
    };

    let h_ac = cancel_width(d, p, a, w1); // Equiv (width_of a c) w1

    // --- H_b : Equiv b (add c w2) ---
    let h_b = {
        let unc_ab = uncancel_width(d, p, a, b); // Equiv b (add a width_ab)
        let a_width_ab = cadd(d, p, a, width_ab);
        let w1w2 = cadd(d, p, w1, w2);
        let a_w1w2 = cadd(d, p, a, w1w2);
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        let step1 = d.lemma(p.add_congr, &[a, a, width_ab, w1w2, refl_a, h_split]);

        let c_w2 = cadd(d, p, c, w2);
        let assoc = d.lemma(p.add_assoc, &[a, w1, w2]); // Equiv c_w2 a_w1w2
        let step2 = d.lemma(p.equiv_symm, &[c_w2, a_w1w2, assoc]); // Equiv a_w1w2 c_w2

        echain(
            d,
            p,
            b,
            &[(a_width_ab, unc_ab), (a_w1w2, step1), (c_w2, step2)],
        )
    };

    // --- H_cb : Equiv (width_of c b) w2 ---
    let h_cb = {
        let neg_c = cneg(d, p, c);
        let start = width_of(d, p, c, b); // add b (neg c)
        let c_w2 = cadd(d, p, c, w2);
        let refl_neg_c = d.lemma(p.equiv_refl, &[neg_c]);
        let cw2_negc = cadd(d, p, c_w2, neg_c);
        let step1 = d.lemma(p.add_congr, &[b, c_w2, neg_c, neg_c, h_b, refl_neg_c]);
        let cancel = cancel_width(d, p, c, w2); // Equiv cw2_negc w2

        echain(d, p, start, &[(cw2_negc, step1), (w2, cancel)])
    };

    // --- deltas ---
    let frac_ac = frac_of(d, p, m_ac);
    let width_ac = width_of(d, p, a, c);
    let delta_ac = delta_of(d, p, a, c, m_ac);
    let h_delta_ac = delta_from_width_equiv(
        d, p, width_ac, h_ac, w1, delta_ab, on_ac, frac_ac, delta_ac, m_ac,
    );

    let frac_cb = frac_of(d, p, m_cb);
    let width_cb = width_of(d, p, c, b);
    let delta_cb = delta_of(d, p, c, b, m_cb);
    let h_delta_cb = delta_from_width_equiv(
        d, p, width_cb, h_cb, w2, delta_ab, on_cb, frac_cb, delta_cb, m_cb,
    );

    // --- piece 1 : Equiv (sumRange f_ab n_ac) (riemannSum F a c m_ac) ---
    let f_ab = summand_fn(d, p, f, a, delta_ab);
    let f_ac = summand_fn(d, p, f, a, delta_ac);
    let pointwise1 = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let oi = d.const_app(p.of_nat, &[i]);
        let sp_ab = sample_point(d, p, a, delta_ab, i);
        let sp_ac = sample_point(d, p, a, delta_ac, i);

        let symm_ac1 = d.lemma(p.equiv_symm, &[delta_ac, delta_ab, h_delta_ac]);
        let refl_oi = d.lemma(p.equiv_refl, &[oi]);
        let mc = d.lemma(
            p.mul_congr,
            &[oi, oi, delta_ab, delta_ac, refl_oi, symm_ac1],
        );
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        let oi_delta_ab = cmul(d, p, oi, delta_ab);
        let oi_delta_ac = cmul(d, p, oi, delta_ac);
        let h_sp = d.lemma(p.add_congr, &[a, a, oi_delta_ab, oi_delta_ac, refl_a, mc]);

        let f_spab = d.apply(f, &[sp_ab]);
        let f_spac = d.apply(f, &[sp_ac]);
        let hcong_i = d.apply(hcong, &[sp_ab, sp_ac, h_sp]);
        let symm_ac2 = d.lemma(p.equiv_symm, &[delta_ac, delta_ab, h_delta_ac]);
        let final_i = d.lemma(
            p.mul_congr,
            &[f_spab, f_spac, delta_ab, delta_ac, hcong_i, symm_ac2],
        );

        d.lam_fv(i_fv, nat, final_i)
    };
    let piece1 = d.lemma(p.sum_range_congr, &[f_ab, f_ac, n_ac, pointwise1]);

    // --- piece 2 : Equiv (sumRange (shifted n_ac f_ab) n_cb) (riemannSum F c b m_cb) ---
    let f_cb = summand_fn(d, p, f, c, delta_cb);
    let f_ab_shifted = shifted_fn(d, n_ac, f_ab);
    let pointwise2 = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ok = d.const_app(p.of_nat, &[k]);
        let nack = NatOps::add(d, n_ac, k);
        let onack = d.const_app(p.of_nat, &[nack]);
        let sp_shift = sample_point(d, p, a, delta_ab, nack);
        let sp_cb = sample_point(d, p, c, delta_cb, k);

        let of_nat_add_step = d.lemma(p.of_nat_add, &[n_ac, k]); // Equiv onack (add on_ac ok)
        let sum_on2 = cadd(d, p, on_ac, ok);
        let refl_delta_ab2 = d.lemma(p.equiv_refl, &[delta_ab]);
        let mul_onack_delta = cmul(d, p, onack, delta_ab);
        let mul_sumon2_delta = cmul(d, p, sum_on2, delta_ab);
        let step_m1 = d.lemma(
            p.mul_congr,
            &[
                onack,
                sum_on2,
                delta_ab,
                delta_ab,
                of_nat_add_step,
                refl_delta_ab2,
            ],
        );

        let ok_delta_ab = cmul(d, p, ok, delta_ab);
        let add_w1_okdab = cadd(d, p, w1, ok_delta_ab);
        let step_rd = right_distrib(d, p, on_ac, ok, delta_ab); // Equiv mul_sumon2_delta add_w1_okdab

        let chain_inner = echain(
            d,
            p,
            mul_onack_delta,
            &[(mul_sumon2_delta, step_m1), (add_w1_okdab, step_rd)],
        );

        let a_add_w1_okdab = cadd(d, p, a, add_w1_okdab);
        let refl_a2 = d.lemma(p.equiv_refl, &[a]);
        let step_outer = d.lemma(
            p.add_congr,
            &[a, a, mul_onack_delta, add_w1_okdab, refl_a2, chain_inner],
        );

        let c_add_okdab = cadd(d, p, c, ok_delta_ab);
        let assoc3 = d.lemma(p.add_assoc, &[a, w1, ok_delta_ab]); // Equiv c_add_okdab a_add_w1_okdab
        let assoc3_symm = d.lemma(p.equiv_symm, &[c_add_okdab, a_add_w1_okdab, assoc3]);

        let symm_cb1 = d.lemma(p.equiv_symm, &[delta_cb, delta_ab, h_delta_cb]);
        let refl_ok = d.lemma(p.equiv_refl, &[ok]);
        let step_okdelta = d.lemma(
            p.mul_congr,
            &[ok, ok, delta_ab, delta_cb, refl_ok, symm_cb1],
        );
        let ok_delta_cb = cmul(d, p, ok, delta_cb);
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        let step_final_inner = d.lemma(
            p.add_congr,
            &[c, c, ok_delta_ab, ok_delta_cb, refl_c, step_okdelta],
        );

        let h_sp2 = echain(
            d,
            p,
            sp_shift,
            &[
                (a_add_w1_okdab, step_outer),
                (c_add_okdab, assoc3_symm),
                (sp_cb, step_final_inner),
            ],
        );

        let f_spshift = d.apply(f, &[sp_shift]);
        let f_spcb = d.apply(f, &[sp_cb]);
        let hcong_k = d.apply(hcong, &[sp_shift, sp_cb, h_sp2]);
        let symm_cb2 = d.lemma(p.equiv_symm, &[delta_cb, delta_ab, h_delta_cb]);
        let final_k = d.lemma(
            p.mul_congr,
            &[f_spshift, f_spcb, delta_ab, delta_cb, hcong_k, symm_cb2],
        );

        d.lam_fv(k_fv, nat, final_k)
    };
    let piece2 = d.lemma(p.sum_range_congr, &[f_ab_shifted, f_cb, n_cb, pointwise2]);

    // --- assemble ---
    let split = d.lemma(p.sum_range_split, &[f_ab, n_ac, n_cb]);
    let sum_f_ab_nac = d.const_app(p.sum_range, &[f_ab, n_ac]);
    let sum_shifted_ncb = d.const_app(p.sum_range, &[f_ab_shifted, n_cb]);
    let riemann_ac = rsum(d, p, f, a, c, m_ac);
    let riemann_cb = rsum(d, p, f, c, b, m_cb);
    let combine = d.lemma(
        p.add_congr,
        &[
            sum_f_ab_nac,
            riemann_ac,
            sum_shifted_ncb,
            riemann_cb,
            piece1,
            piece2,
        ],
    );

    let sum_split_domain = NatOps::add(d, n_ac, n_cb);
    let sumrange_full = d.const_app(p.sum_range, &[f_ab, sum_split_domain]);
    let combined_rhs = cadd(d, p, sum_f_ab_nac, sum_shifted_ncb);
    let target_rhs = cadd(d, p, riemann_ac, riemann_cb);
    let proof = d.lemma(
        p.equiv_trans,
        &[sumrange_full, combined_rhs, target_rhs, split, combine],
    );

    let ty = {
        let lhs = rsum(d, p, f, a, b, m_ab);
        let concl = equiv(d, p, lhs, target_rhs);
        let over_hcong = d.arrow(hcong_ty, concl);
        let over_mcb = d.pi_fv(mcb_fv, nat, over_hcong);
        let over_mac = d.pi_fv(mac_fv, nat, over_mcb);
        let over_b = d.pi_fv(b_fv, carrier, over_mac);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let over_hcong = d.lam_fv(hcong_fv, hcong_ty, proof);
        let over_mcb = d.lam_fv(mcb_fv, nat, over_hcong);
        let over_mac = d.lam_fv(mac_fv, nat, over_mcb);
        let over_b = d.lam_fv(b_fv, carrier, over_mac);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_split_exact,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.integral_split`, gap 1: the accuracy-parameterized mesh family
// and its `c`-independence ----------------------------------------------
//
// `riemannSum_split_exact`'s split point `c := a + (ofNat (succ m_ac)) *
// delta_of a b (add (succ m_ac) m_cb)` depends on the CHOSEN counts
// `(m_ac, m_cb)`, not just on their ratio. `riemannSum_integral_close`
// (well above) needs the mesh count to clear an accuracy-`e`-dependent
// Archimedean threshold on ALL THREE intervals simultaneously. The natural
// family fixes a ratio once (`m_ac0`/`m_cb0`) and scales BOTH sub-counts by
// the SAME factor `Nat.succ k`, via [`succ_mul_succ`] (so `succ (m_ac at k)
// = (succ m_ac0)*(succ k)` EXACTLY, not merely close, and likewise for
// `m_cb`) — and this section shows the resulting `c` does not move at all
// as `k` grows, so `k` is free to be chosen purely to satisfy the accuracy
// threshold, with no back-reaction on which split point the family
// approximates.
//
// The pure `Nat`/`Rat` half of the argument (`delta_of a b m` scales down by
// EXACTLY `1/(succ k)` when `m` is refined by [`succ_mul_succ`]) is isolated
// in [`mesh_scale_by_succ_k`], via [`CRealPrelude::mesh_reciprocal_mul`] (the
// exact reciprocal-mesh identity) and [`mesh_inverse_identity`] (cancelling
// the introduced `succ k` factor back out) — the same two pieces
// `riemannSum_cauchy`'s own common-refinement chain already leans on,
// reused rather than re-derived.

/// Given `a, b, m_ab0, k : Nat`/`CReal`, returns `(m_ab_prime, proof)` where
/// `m_ab_prime := `[`succ_mul_succ`]`(m_ab0, k).0` (so `Nat.succ m_ab_prime`
/// is definitionally `(Nat.succ m_ab0)*(Nat.succ k)`) and
///
/// `proof : Equiv (mul (ofNat (Nat.succ k)) (delta_of a b m_ab_prime))
///                (delta_of a b m_ab0)`
///
/// — refining the SAME interval `[a, b]`'s mesh by a factor `Nat.succ k`
/// scales its step down by EXACTLY `1/(Nat.succ k)`, not merely closely.
///
/// Route: [`CRealPrelude::mesh_reciprocal_mul`] gives `natDivSucc 1 m_ab0 *
/// natDivSucc 1 k = natDivSucc 1 m_ab_prime` EXACTLY (Rat-level `Eq`); lifted
/// to `CReal` via [`CRealPrelude::of_rat_mul`], the goal becomes an
/// eight-atom associativity/commutativity rearrangement — identical in kind
/// to [`mesh_times_count_eq_width`]'s and [`riemann_sum_const_core`]'s own
/// rearrangements, just with two extra factors — landing on `(width_ab *
/// embed(natDivSucc 1 m_ab0)) * (ofNat (succ k) * embed(natDivSucc 1 k))`,
/// and [`mesh_inverse_identity`] cancels the second parenthesis to `one`.
fn mesh_scale_by_succ_k(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    m_ab0: ExprId,
    k: ExprId,
) -> (ExprId, ExprId) {
    let (m_ab_prime, _pf_ab) = succ_mul_succ(d, m_ab0, k);
    let width_ab = width_of(d, p, a, b);
    let succ_k = d.succ(k);
    let on_succ_k = d.const_app(p.of_nat, &[succ_k]);

    let one_nat = d.num(1);
    let fr_ab0 = d.const_app(p.rat.nat_div_succ, &[one_nat, m_ab0]);
    let fr_k = d.const_app(p.rat.nat_div_succ, &[one_nat, k]);
    let fr_prime = d.const_app(p.rat.nat_div_succ, &[one_nat, m_ab_prime]);

    let embed_ab0 = embed(d, p, fr_ab0);
    let embed_k = embed(d, p, fr_k);
    let embed_prime = embed(d, p, fr_prime);

    let delta_prime = cmul(d, p, width_ab, embed_prime); // = delta_of(a, b, m_ab_prime)

    // rat_recip : Eq Rat (rmul fr_ab0 fr_k) fr_prime
    let rat_recip = d.lemma(p.mesh_reciprocal_mul, &[m_ab0, k]);
    // of_rat_mul_step : Equiv (mul embed_ab0 embed_k) (embed (rmul fr_ab0 fr_k))
    let of_rat_mul_step = d.lemma(p.of_rat_mul, &[fr_ab0, fr_k]);
    let mul_ab0_k = cmul(d, p, embed_ab0, embed_k);
    let rmul_fr = rmul(d, fr_ab0, fr_k);
    let bridge = rat_eq_rewrite(d, rmul_fr, fr_prime, rat_recip, of_rat_mul_step, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, mul_ab0_k, embedded)
    });
    // bridge : Equiv mul_ab0_k embed_prime
    let bridge_symm = d.lemma(p.equiv_symm, &[mul_ab0_k, embed_prime, bridge]);
    // bridge_symm : Equiv embed_prime mul_ab0_k

    // Atoms: A := on_succ_k, B := width_ab, C := embed_ab0, D := embed_k.
    let a_atom = on_succ_k;
    let b_atom = width_ab;
    let c_atom = embed_ab0;
    let d_atom = embed_k;

    let cd = cmul(d, p, c_atom, d_atom);
    let b_cd = cmul(d, p, b_atom, cd);
    let refl_b = d.lemma(p.equiv_refl, &[b_atom]);
    let step_inner = d.lemma(
        p.mul_congr,
        &[b_atom, b_atom, embed_prime, cd, refl_b, bridge_symm],
    );
    // step_inner : Equiv delta_prime b_cd

    let a_delta_prime = cmul(d, p, a_atom, delta_prime);
    let a_bcd = cmul(d, p, a_atom, b_cd);
    let refl_a = d.lemma(p.equiv_refl, &[a_atom]);
    let step0 = d.lemma(
        p.mul_congr,
        &[a_atom, a_atom, delta_prime, b_cd, refl_a, step_inner],
    );
    // step0 : Equiv a_delta_prime a_bcd

    let ab = cmul(d, p, a_atom, b_atom);
    let ab_cd = cmul(d, p, ab, cd);
    let masc1 = d.lemma(p.mul_assoc, &[a_atom, b_atom, cd]); // Equiv ab_cd a_bcd
    let step1 = d.lemma(p.equiv_symm, &[ab_cd, a_bcd, masc1]); // Equiv a_bcd ab_cd

    let abc = cmul(d, p, ab, c_atom);
    let abc_d = cmul(d, p, abc, d_atom);
    let masc2 = d.lemma(p.mul_assoc, &[ab, c_atom, d_atom]); // Equiv abc_d ab_cd
    let step2 = d.lemma(p.equiv_symm, &[abc_d, ab_cd, masc2]); // Equiv ab_cd abc_d

    let bc = cmul(d, p, b_atom, c_atom);
    let a_bc = cmul(d, p, a_atom, bc);
    let masc3 = d.lemma(p.mul_assoc, &[a_atom, b_atom, c_atom]); // Equiv abc a_bc
    let bc_a = cmul(d, p, bc, a_atom);
    let mcomm3 = d.lemma(p.mul_comm, &[a_atom, bc]); // Equiv a_bc bc_a
    let chain3 = d.lemma(p.equiv_trans, &[abc, a_bc, bc_a, masc3, mcomm3]); // Equiv abc bc_a

    let bca_d = cmul(d, p, bc_a, d_atom);
    let refl_d = d.lemma(p.equiv_refl, &[d_atom]);
    let step4 = d.lemma(p.mul_congr, &[abc, bc_a, d_atom, d_atom, chain3, refl_d]);
    // step4 : Equiv abc_d bca_d

    let a_d = cmul(d, p, a_atom, d_atom);
    let bc_ad = cmul(d, p, bc, a_d);
    let masc5 = d.lemma(p.mul_assoc, &[bc, a_atom, d_atom]); // Equiv bca_d bc_ad

    let mii = mesh_inverse_identity(d, p, k); // Equiv a_d one
    let one_c = d.kernel().const_(p.one, vec![]);
    let refl_bc = d.lemma(p.equiv_refl, &[bc]);
    let step6 = d.lemma(p.mul_congr, &[bc, bc, a_d, one_c, refl_bc, mii]);
    // step6 : Equiv bc_ad (mul bc one)
    let bc_one = cmul(d, p, bc, one_c);
    let step7 = d.lemma(p.mul_one, &[bc]); // Equiv bc_one bc

    let proof = echain(
        d,
        p,
        a_delta_prime,
        &[
            (a_bcd, step0),
            (ab_cd, step1),
            (abc_d, step2),
            (bca_d, step4),
            (bc_ad, masc5),
            (bc_one, step6),
            (bc, step7),
        ],
    );
    // proof : Equiv a_delta_prime bc, i.e. Equiv (mul on_succ_k delta_prime)
    // delta_ab0 (`bc = mul width_ab embed_ab0 = delta_of a b m_ab0` exactly).
    (m_ab_prime, proof)
}

/// Admit `CReal.riemannSum_split_scale_invariant`: fixing a ratio
/// `(m_ac0, m_cb0)` once and scaling BOTH sub-counts by the same factor
/// `Nat.succ k` (via [`succ_mul_succ`]) leaves
/// [`CRealPrelude::riemann_sum_split_exact`]'s own split point `c`
/// UNCHANGED — `Equiv c_k c_0` for every `k`, where `c_k`/`c_0` are
/// `riemannSum_split_exact`'s `c` formula read at the scaled/base counts.
///
/// This is gap 1 of `integral_split`'s remaining assembly (see this file's
/// own module documentation, "the accuracy-parameterized mesh choice"): it
/// makes `k` free to pick however deep `riemannSum_integral_close` needs on
/// all three intervals, without moving the split point the family
/// approximates. The two scaled counts themselves
/// (`succ_mul_succ(m_ac0, k).0`, `succ_mul_succ(m_cb0, k).0`) are exactly
/// the `(m_ac(e), m_cb(e))` a caller would use at whichever `k` clears the
/// accuracy threshold.
///
/// Proof: [`mesh_scale_by_succ_k`] at `(a, b, m_ab0, k)` gives the pure
/// mesh-scaling identity for the COMBINED interval's own step; a `Nat`
/// bookkeeping chain (`Nat.right_distrib` plus two more
/// [`succ_mul_succ`] witnesses, closed with `Nat.succ_injective` to strip
/// the outer `Nat.succ`) shows the scaled COMBINED count
/// `riemannSum_split_exact` itself would compute at `(m_ac(k), m_cb(k))` —
/// `add (succ (succ_mul_succ(m_ac0,k).0)) (succ_mul_succ(m_cb0,k).0)` —
/// literally EQUALS [`mesh_scale_by_succ_k`]'s own `m_ab_prime`; then
/// [`CRealPrelude::of_nat_mul`] turns the scaled `m_ac` count's own
/// `Nat.succ` shape into `(succ m_ac0) * (succ k)`, and the same
/// `mul_assoc`/`mul_congr` idiom folds everything down to `Equiv c_k c_0`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_split_scale_invariant(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let np = d.prelude();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let mac0_fv = d.fresh_fvar();
    let m_ac0 = d.kernel().fvar(mac0_fv);
    let mcb0_fv = d.fresh_fvar();
    let m_cb0 = d.kernel().fvar(mcb0_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let n_ac0 = d.succ(m_ac0);
    let n_cb0 = d.succ(m_cb0);
    let succ_k = d.succ(k);
    let m_ab0 = NatOps::add(d, n_ac0, m_cb0);

    let (m_ac_k, pf_ac) = succ_mul_succ(d, m_ac0, k); // Eq Nat (mul n_ac0 succ_k) n_ac_k
    let (m_cb_k, pf_cb) = succ_mul_succ(d, m_cb0, k); // Eq Nat (mul n_cb0 succ_k) n_cb_k
    let n_ac_k = d.succ(m_ac_k);
    let n_cb_k = d.succ(m_cb_k);
    let m_ab_k = NatOps::add(d, n_ac_k, m_cb_k); // riemannSum_split_exact's own "m_ab" at (m_ac_k, m_cb_k)

    let (m_ab_prime, h_scale) = mesh_scale_by_succ_k(d, p, a, b, m_ab0, k);

    // --- Nat bookkeeping: Eq Nat m_ab_k m_ab_prime ---
    let mul_ac = NatOps::mul(d, n_ac0, succ_k);
    let mul_cb = NatOps::mul(d, n_cb0, succ_k);

    let pf_ac_symm = d.symm(mul_ac, n_ac_k, pf_ac); // Eq Nat n_ac_k mul_ac
    let step_a = d.congr(n_ac_k, mul_ac, pf_ac_symm, &|d, x| {
        NatOps::add(d, x, n_cb_k)
    });
    // step_a : Eq Nat (add n_ac_k n_cb_k) (add mul_ac n_cb_k)

    let pf_cb_symm = d.symm(mul_cb, n_cb_k, pf_cb); // Eq Nat n_cb_k mul_cb
    let step_b = d.congr(n_cb_k, mul_cb, pf_cb_symm, &|d, x| {
        NatOps::add(d, mul_ac, x)
    });
    // step_b : Eq Nat (add mul_ac n_cb_k) (add mul_ac mul_cb)

    let n_ab0 = NatOps::add(d, n_ac0, n_cb0);
    let rd = d.lemma(np.right_distrib, &[n_ac0, n_cb0, succ_k]);
    // rd : Eq Nat (mul n_ab0 succ_k) (add mul_ac mul_cb)
    let add_ac_cb = NatOps::add(d, mul_ac, mul_cb);
    let mul_n_ab0_succk = NatOps::mul(d, n_ab0, succ_k);
    let step_c = d.symm(mul_n_ab0_succk, add_ac_cb, rd); // Eq Nat add_ac_cb mul_n_ab0_succk

    let (m_ab_prime2, pf_ab) = succ_mul_succ(d, m_ab0, k);
    debug_assert_eq!(m_ab_prime, m_ab_prime2);
    // pf_ab : Eq Nat (mul (succ m_ab0) succ_k) (succ m_ab_prime), and
    // `succ m_ab0` is definitionally `n_ab0` (both `add n_ac0 (succ m_cb0)`
    // reduce to `succ (add n_ac0 m_cb0)`), so `pf_ab` is directly usable at
    // `Eq Nat mul_n_ab0_succk (succ m_ab_prime)`.

    let nack_ncbk = NatOps::add(d, n_ac_k, n_cb_k);
    let mulac_ncbk = NatOps::add(d, mul_ac, n_cb_k);
    let succ_m_ab_prime = d.succ(m_ab_prime);
    let (_, h_succ_eq) = d.chain(
        nack_ncbk,
        &[
            (mulac_ncbk, step_a),
            (add_ac_cb, step_b),
            (mul_n_ab0_succk, step_c),
            (succ_m_ab_prime, pf_ab),
        ],
    );
    // h_succ_eq : Eq Nat (add n_ac_k n_cb_k) (succ m_ab_prime), and
    // `add n_ac_k n_cb_k` is definitionally `succ (add n_ac_k m_cb_k)` =
    // `succ m_ab_k` (add recurses on its right, succ-shaped, argument), so
    // this is directly usable at `Eq Nat (succ m_ab_k) (succ m_ab_prime)`.
    let h_ab_eq = d.lemma(np.succ_injective, &[m_ab_k, m_ab_prime, h_succ_eq]);
    // h_ab_eq : Eq Nat m_ab_k m_ab_prime

    // --- bridge delta_of(a,b,m_ab_k) ~ delta_of(a,b,m_ab_prime) ---
    let width_ab = width_of(d, p, a, b);
    let delta_ab_k = delta_of(d, p, a, b, m_ab_k);
    let delta_ab0 = delta_of(d, p, a, b, m_ab0);
    let one_nat = d.num(1);
    let fr_k_exp = d.const_app(p.rat.nat_div_succ, &[one_nat, m_ab_k]);
    let fr_prime_exp = d.const_app(p.rat.nat_div_succ, &[one_nat, m_ab_prime]);
    let rat_eq_km = nat_eq_to_rat(d, m_ab_k, m_ab_prime, h_ab_eq, &|d, x| {
        d.const_app(p.rat.nat_div_succ, &[one_nat, x])
    });
    // rat_eq_km : Eq Rat fr_k_exp fr_prime_exp
    let refl_delta_k = d.lemma(p.equiv_refl, &[delta_ab_k]);
    let h_delta_k_prime = rat_eq_rewrite(
        d,
        fr_k_exp,
        fr_prime_exp,
        rat_eq_km,
        refl_delta_k,
        &|d, t| {
            let embedded = embed(d, p, t);
            let rhs = cmul(d, p, width_ab, embedded);
            equiv(d, p, delta_ab_k, rhs)
        },
    );
    // h_delta_k_prime : Equiv delta_ab_k (delta_of a b m_ab_prime)

    let on_succ_k = d.const_app(p.of_nat, &[succ_k]);
    let refl_succk = d.lemma(p.equiv_refl, &[on_succ_k]);
    let embed_prime_exp = embed(d, p, fr_prime_exp);
    let delta_ab_prime = cmul(d, p, width_ab, embed_prime_exp);
    let step_y1 = d.lemma(
        p.mul_congr,
        &[
            on_succ_k,
            on_succ_k,
            delta_ab_k,
            delta_ab_prime,
            refl_succk,
            h_delta_k_prime,
        ],
    );
    // step_y1 : Equiv (mul on_succ_k delta_ab_k) (mul on_succ_k delta_ab_prime)
    let succk_deltak = cmul(d, p, on_succ_k, delta_ab_k);
    let succk_deltaprime = cmul(d, p, on_succ_k, delta_ab_prime);
    let h_scale_full = d.lemma(
        p.equiv_trans,
        &[succk_deltak, succk_deltaprime, delta_ab0, step_y1, h_scale],
    );
    // h_scale_full : Equiv (mul on_succ_k delta_ab_k) delta_ab0

    // --- E_ac : Equiv (ofNat n_ac_k) (mul (ofNat n_ac0) on_succ_k) ---
    let of_nat_mul_ac = d.lemma(p.of_nat_mul, &[n_ac0, succ_k]);
    let ofnat_nac0 = d.const_app(p.of_nat, &[n_ac0]);
    let rhs_ac = cmul(d, p, ofnat_nac0, on_succ_k);
    let e_ac = nat_rewrite_prop(d, mul_ac, n_ac_k, pf_ac, of_nat_mul_ac, &|d, x| {
        let ofx = d.const_app(p.of_nat, &[x]);
        equiv(d, p, ofx, rhs_ac)
    });
    // e_ac : Equiv (ofNat n_ac_k) rhs_ac

    // --- combine: ofNat(n_ac_k) * delta_ab_k ~ ofNat(n_ac0) * delta_ab0 ---
    let ofnat_nack = d.const_app(p.of_nat, &[n_ac_k]);
    let refl_delta_ab_k2 = d.lemma(p.equiv_refl, &[delta_ab_k]);
    let step_x1 = d.lemma(
        p.mul_congr,
        &[
            ofnat_nack,
            rhs_ac,
            delta_ab_k,
            delta_ab_k,
            e_ac,
            refl_delta_ab_k2,
        ],
    );
    // step_x1 : Equiv (mul ofnat_nack delta_ab_k) (mul rhs_ac delta_ab_k)
    let masc_x = d.lemma(p.mul_assoc, &[ofnat_nac0, on_succ_k, delta_ab_k]);
    // masc_x : Equiv (mul rhs_ac delta_ab_k) (mul ofnat_nac0 (mul on_succ_k delta_ab_k))
    let refl_nac0 = d.lemma(p.equiv_refl, &[ofnat_nac0]);
    let nac0_succk_deltak = cmul(d, p, ofnat_nac0, succk_deltak);
    let nac0_delta0 = cmul(d, p, ofnat_nac0, delta_ab0);
    let step_x2 = d.lemma(
        p.mul_congr,
        &[
            ofnat_nac0,
            ofnat_nac0,
            succk_deltak,
            delta_ab0,
            refl_nac0,
            h_scale_full,
        ],
    );
    // step_x2 : Equiv (mul ofnat_nac0 (mul on_succ_k delta_ab_k)) (mul ofnat_nac0 delta_ab0)

    let nack_deltak = cmul(d, p, ofnat_nack, delta_ab_k);
    let rhsac_deltak = cmul(d, p, rhs_ac, delta_ab_k);
    let h_offset = echain(
        d,
        p,
        nack_deltak,
        &[
            (rhsac_deltak, step_x1),
            (nac0_succk_deltak, masc_x),
            (nac0_delta0, step_x2),
        ],
    );
    // h_offset : Equiv (mul (ofNat n_ac_k) delta_ab_k) (mul (ofNat n_ac0) delta_ab0)

    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let c_k = cadd(d, p, a, nack_deltak);
    let c_0 = cadd(d, p, a, nac0_delta0);
    let proof = d.lemma(
        p.add_congr,
        &[a, a, nack_deltak, nac0_delta0, refl_a, h_offset],
    );
    // proof : Equiv c_k c_0

    let concl = equiv(d, p, c_k, c_0);
    let ty = {
        let over_k = d.pi_fv(k_fv, nat, concl);
        let over_mcb0 = d.pi_fv(mcb0_fv, nat, over_k);
        let over_mac0 = d.pi_fv(mac0_fv, nat, over_mcb0);
        let over_b = d.pi_fv(b_fv, carrier, over_mac0);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let over_k = d.lam_fv(k_fv, nat, proof);
        let over_mcb0 = d.lam_fv(mcb0_fv, nat, over_k);
        let over_mac0 = d.lam_fv(mac0_fv, nat, over_mcb0);
        let over_b = d.lam_fv(b_fv, carrier, over_mac0);
        d.lam_fv(a_fv, carrier, over_b)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_split_scale_invariant,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.congrOfUniformlyContinuous : ∀ F a b, UniformlyContinuousOn F a b →
/// ∀ x y, le a x → le x b → le a y → le y b → Equiv x y → Equiv (F x) (F y)`
/// — the DOMAIN-RESTRICTED half of [`CRealPrelude::riemann_sum_split_exact`]'s
/// `hcong` hypothesis, derived directly from a uniform-continuity witness.
///
/// **This is restricted to `x, y ∈ [a, b]`, and cannot be strengthened to the
/// GLOBAL `∀ x y, Equiv x y → Equiv (F x) (F y)` `riemannSum_split_exact`
/// actually demands, for a structural reason, not a missing lemma**:
/// `UniformlyContinuousOn F a b`'s own `spec` says nothing about `F` outside
/// `[a, b]` at all (`uc_spec_body`'s hypothesis list requires `a ≤ x ≤ b` and
/// `a ≤ y ≤ b`), so a genuinely global `hcong` is simply FALSE for an
/// arbitrary uniformly-continuous-on-`[a,b]` `F` (nothing constrains its
/// values elsewhere). Using this lemma to discharge `riemannSum_split_exact`'s
/// `hcong` at a concrete `(F, a, b, u)` therefore additionally needs each
/// sample point `riemannSum_split_exact`'s own proof applies `hcong` to to be
/// shown inside `[a, b]` first (e.g. via
/// [`CRealPrelude::riemann_sample_in_bounds`]-style reasoning) — not attempted
/// here, and it is a SEPARATE, bounded gap from this lemma's own construction.
///
/// Route: EXACTLY [`pointwise_block_equiv`]'s own middle section
/// (`CRealPrelude::equiv_abs_diff_le` turning `Equiv x y` into an abs bound at
/// every accuracy, `UniformlyContinuousOn.spec` promoting it through `F`,
/// `CRealPrelude::equiv_zero_of_small` + [`equiv_of_sub_equiv_zero_local`]
/// closing the resulting `∀ e, …` bound into a full `Equiv`) — reused
/// verbatim rather than duplicated, since this file already builds it for
/// the reblock chain.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_congr_of_uniformly_continuous(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let hax_ty = cle(d, p, a, x);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hxb_ty = cle(d, p, x, b);
    let hxb_fv = d.fresh_fvar();
    let hxb = d.kernel().fvar(hxb_fv);
    let hay_ty = cle(d, p, a, y);
    let hay_fv = d.fresh_fvar();
    let hay = d.kernel().fvar(hay_fv);
    let hyb_ty = cle(d, p, y, b);
    let hyb_fv = d.fresh_fvar();
    let hyb = d.kernel().fvar(hyb_fv);

    let hxy_ty = equiv(d, p, x, y);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);

    let f_x = d.apply(f, &[x]);
    let f_y = d.apply(f, &[y]);
    let neg_fy = cneg(d, p, f_y);
    let v = cadd(d, p, f_x, neg_fy);

    let hyp_small = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
        let mod_e = d.apply(modulus_fn, &[e]);
        let hclose_input = d.lemma(p.equiv_abs_diff_le, &[x, y, hxy, mod_e]);
        let spec_out = d.lemma(
            p.uc_spec,
            &[f, a, b, u, e, x, y, hax, hxb, hay, hyb, hclose_input],
        );
        d.lam_fv(e_fv, nat, spec_out)
    };
    let v_equiv_zero = d.lemma(p.equiv_zero_of_small, &[v, hyp_small]);
    let concl_proof = equiv_of_sub_equiv_zero_local(d, p, f_x, f_y, v_equiv_zero);

    let concl_ty = equiv(d, p, f_x, f_y);

    let ty = {
        let after_hxy = d.arrow(hxy_ty, concl_ty);
        let after_hyb = d.arrow(hyb_ty, after_hxy);
        let after_hay = d.arrow(hay_ty, after_hyb);
        let after_hxb = d.arrow(hxb_ty, after_hay);
        let after_hax = d.arrow(hax_ty, after_hxb);
        let over_y = d.pi_fv(y_fv, carrier, after_hax);
        let over_x = d.pi_fv(x_fv, carrier, over_y);
        let after_u = d.arrow(u_ty, over_x);
        let over_b = d.pi_fv(b_fv, carrier, after_u);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_hxy = d.lam_fv(hxy_fv, hxy_ty, concl_proof);
        let with_hyb = d.lam_fv(hyb_fv, hyb_ty, with_hxy);
        let with_hay = d.lam_fv(hay_fv, hay_ty, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, hxb_ty, with_hay);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxb);
        let over_y = d.lam_fv(y_fv, carrier, with_hax);
        let over_x = d.lam_fv(x_fv, carrier, over_y);
        let with_u = d.lam_fv(u_fv, u_ty, over_x);
        let over_b = d.lam_fv(b_fv, carrier, with_u);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.congr_of_uniformly_continuous,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.riemannSum_split_exact_of_uc : ∀ F a b m_ac m_cb,
/// UniformlyContinuousOn F a b → le a b → Equiv (riemannSum F a b (add
/// (Nat.succ m_ac) m_cb)) (add (riemannSum F a c m_ac) (riemannSum F c b
/// m_cb))`, `c` exactly as in [`declare_riemann_sum_split_exact`].
///
/// [`declare_riemann_sum_split_exact`]'s own `hcong` hypothesis (`∀ x y,
/// Equiv x y → Equiv (F x) (F y)`, GLOBAL) is genuinely false for an
/// arbitrary `F` uniformly continuous only on `[a, b]`
/// ([`declare_congr_of_uniformly_continuous`]'s own doc comment: `spec`
/// says nothing about `F` outside `[a, b]`). This variant discharges the
/// SAME identity from a `UniformlyContinuousOn` witness instead --
/// [`declare_riemann_sum_split_exact`] itself is UNCHANGED, both theorems
/// exist.
///
/// Route: every sample point the original proof's two `sumRange`-congruence
/// steps touch is shown inside `[a, b]` first
/// ([`CRealPrelude::riemann_sample_in_bounds`], read at the parent mesh
/// count `m_ab` for the "shifted" indices and at the two child mesh counts
/// `m_ac`/`m_cb` for the per-child indices, the two child intervals placed
/// inside `[a, b]` via `hac : le a c` / `hcb : le c b` derived here from
/// `w1`/`w2`'s nonnegativity exactly as
/// [`declare_riemann_sample_in_bounds`]'s own lower half does), then
/// [`CRealPrelude::congr_of_uniformly_continuous`] is applied there instead
/// of the (unavailable) global congruence. Since a term of `hcong`'s own
/// GLOBAL `Pi`-type is exactly what is unavailable, the two
/// `sumRange`-congruence steps use the file-local BOUNDED analogue
/// [`sum_range_congr_lt_proof`] (via [`bounded_equiv_pointwise`]) in place of
/// [`CRealPrelude::sum_range_congr`] -- the same substitution
/// [`declare_reblock_block_eq_fine_block_sum`] already makes for the same
/// reason.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_riemann_sum_split_exact_of_uc(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let mac_fv = d.fresh_fvar();
    let m_ac = d.kernel().fvar(mac_fv);
    let mcb_fv = d.fresh_fvar();
    let m_cb = d.kernel().fvar(mcb_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let n_ac = d.succ(m_ac);
    let n_cb = d.succ(m_cb);
    let m_ab = NatOps::add(d, n_ac, m_cb);
    let succ_m_ab = d.succ(m_ab);

    let (delta_ab, delta_ab_nonneg) = delta_nonneg_of(d, p, a, b, m_ab, hab);
    let width_ab = width_of(d, p, a, b);

    let on_ac = d.const_app(p.of_nat, &[n_ac]);
    let on_cb = d.const_app(p.of_nat, &[n_cb]);
    let w1 = cmul(d, p, on_ac, delta_ab);
    let w2 = cmul(d, p, on_cb, delta_ab);
    let c = cadd(d, p, a, w1);

    // --- H_split : Equiv width_ab (add w1 w2) --- IDENTICAL algebra to
    // `declare_riemann_sum_split_exact`; duplicated (rather than shared)
    // since that function is not factored into reusable pieces.
    let h_split = {
        let mcw_ab = d.lemma(p.mesh_count_width, &[width_ab, m_ab]);
        let sm_ab = d.succ(m_ab);
        let on_sm_ab = d.const_app(p.of_nat, &[sm_ab]);
        let mid0 = cmul(d, p, on_sm_ab, delta_ab);
        let hw_ab = d.lemma(p.equiv_symm, &[mid0, width_ab, mcw_ab]);

        let h_ofnat_split = d.lemma(p.of_nat_add, &[n_ac, n_cb]);
        let sum_on = cadd(d, p, on_ac, on_cb);
        let mid1 = cmul(d, p, sum_on, delta_ab);
        let refl_delta_ab = d.lemma(p.equiv_refl, &[delta_ab]);
        let step_a = d.lemma(
            p.mul_congr,
            &[
                on_sm_ab,
                sum_on,
                delta_ab,
                delta_ab,
                h_ofnat_split,
                refl_delta_ab,
            ],
        );

        let add_w1w2 = cadd(d, p, w1, w2);
        let step_b = right_distrib(d, p, on_ac, on_cb, delta_ab);

        echain(
            d,
            p,
            width_ab,
            &[(mid0, hw_ab), (mid1, step_a), (add_w1w2, step_b)],
        )
    };

    let h_ac = cancel_width(d, p, a, w1); // Equiv (width_of a c) w1

    // --- H_b : Equiv b (add c w2) ---
    let h_b = {
        let unc_ab = uncancel_width(d, p, a, b); // Equiv b (add a width_ab)
        let a_width_ab = cadd(d, p, a, width_ab);
        let w1w2 = cadd(d, p, w1, w2);
        let a_w1w2 = cadd(d, p, a, w1w2);
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        let step1 = d.lemma(p.add_congr, &[a, a, width_ab, w1w2, refl_a, h_split]);

        let c_w2 = cadd(d, p, c, w2);
        let assoc = d.lemma(p.add_assoc, &[a, w1, w2]); // Equiv c_w2 a_w1w2
        let step2 = d.lemma(p.equiv_symm, &[c_w2, a_w1w2, assoc]); // Equiv a_w1w2 c_w2

        echain(
            d,
            p,
            b,
            &[(a_width_ab, unc_ab), (a_w1w2, step1), (c_w2, step2)],
        )
    };

    // --- H_cb : Equiv (width_of c b) w2 ---
    let h_cb = {
        let neg_c = cneg(d, p, c);
        let start = width_of(d, p, c, b); // add b (neg c)
        let c_w2 = cadd(d, p, c, w2);
        let refl_neg_c = d.lemma(p.equiv_refl, &[neg_c]);
        let cw2_negc = cadd(d, p, c_w2, neg_c);
        let step1 = d.lemma(p.add_congr, &[b, c_w2, neg_c, neg_c, h_b, refl_neg_c]);
        let cancel = cancel_width(d, p, c, w2); // Equiv cw2_negc w2

        echain(d, p, start, &[(cw2_negc, step1), (w2, cancel)])
    };

    // --- deltas ---
    let frac_ac = frac_of(d, p, m_ac);
    let width_ac = width_of(d, p, a, c);
    let delta_ac = delta_of(d, p, a, c, m_ac);
    let h_delta_ac = delta_from_width_equiv(
        d, p, width_ac, h_ac, w1, delta_ab, on_ac, frac_ac, delta_ac, m_ac,
    );

    let frac_cb = frac_of(d, p, m_cb);
    let width_cb = width_of(d, p, c, b);
    let delta_cb = delta_of(d, p, c, b, m_cb);
    let h_delta_cb = delta_from_width_equiv(
        d, p, width_cb, h_cb, w2, delta_ab, on_cb, frac_cb, delta_cb, m_cb,
    );

    // --- NEW: hac : le a c, hcb : le c b -- from `w1`/`w2`'s
    // nonnegativity, exactly `declare_riemann_sample_in_bounds`'s own lower
    // half. Needed to place BOTH child intervals inside `[a, b]`.
    let on_ac_nonneg = zero_le_of_nat(d, p, n_ac);
    let w1_nonneg = d.lemma(
        p.mul_nonneg,
        &[on_ac, delta_ab, on_ac_nonneg, delta_ab_nonneg],
    );
    let hac = shift_le_of_nonneg(d, p, a, w1, w1_nonneg); // le a (add a w1) = le a c

    let on_cb_nonneg = zero_le_of_nat(d, p, n_cb);
    let w2_nonneg = d.lemma(
        p.mul_nonneg,
        &[on_cb, delta_ab, on_cb_nonneg, delta_ab_nonneg],
    );
    let hcb = {
        let c_w2 = cadd(d, p, c, w2);
        let shifted = shift_le_of_nonneg(d, p, c, w2, w2_nonneg); // le c c_w2
        let refl_c_eq = d.lemma(p.equiv_refl, &[c]);
        let h_b_symm = d.lemma(p.equiv_symm, &[b, c_w2, h_b]); // Equiv c_w2 b
        d.lemma(p.le_congr, &[c, c, c_w2, b, refl_c_eq, h_b_symm, shifted])
        // : le c b
    };

    // --- piece 1 : Equiv (sumRange f_ab n_ac) (riemannSum F a c m_ac) ---
    // BOUNDED pointwise (i < n_ac), unlike `declare_riemann_sum_split_exact`'s
    // global `hcong` application.
    let f_ab = summand_fn(d, p, f, a, delta_ab);
    let f_ac = summand_fn(d, p, f, a, delta_ac);
    let bounded_pointwise1 = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.lt(i, n_ac);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);

        let oi = d.const_app(p.of_nat, &[i]);
        let sp_ab = sample_point(d, p, a, delta_ab, i);
        let sp_ac = sample_point(d, p, a, delta_ac, i);

        // sp_ab in [a, b]: i < n_ac <= succ m_ab via `le_add_right`/`le_succ`/
        // `le_trans`/`lt_of_lt_of_le`, then `riemann_sample_in_bounds` on
        // [a, b] at the parent mesh count `m_ab`.
        let np = d.prelude();
        let n_ac_le_m_ab = d.lemma(np.le_add_right, &[n_ac, m_cb]); // le n_ac m_ab
        let m_ab_le_succ_m_ab = d.lemma(np.le_succ, &[m_ab]); // le m_ab succ_m_ab
        let n_ac_le_succ_mab = d.lemma(
            np.le_trans,
            &[n_ac, m_ab, succ_m_ab, n_ac_le_m_ab, m_ab_le_succ_m_ab],
        );
        let hi_succ_mab = d.lemma(
            np.lt_of_lt_of_le,
            &[i, n_ac, succ_m_ab, hi, n_ac_le_succ_mab],
        );
        let and_ab = d.lemma(
            p.riemann_sample_in_bounds,
            &[a, b, m_ab, i, hab, hi_succ_mab],
        );
        let a_le_spab_ty = cle(d, p, a, sp_ab);
        let spab_le_b_ty = cle(d, p, sp_ab, b);
        let a_le_spab = d.const_app(logic.and_left, &[a_le_spab_ty, spab_le_b_ty, and_ab]);
        let spab_le_b = d.const_app(logic.and_right, &[a_le_spab_ty, spab_le_b_ty, and_ab]);

        // sp_ac in [a, b]: directly in [a, c] via `riemann_sample_in_bounds`
        // at the EXACT bound `i < n_ac` (`m_ac`'s own mesh count), then
        // `c <= b` (`hcb`) extends the upper bound.
        let and_ac = d.lemma(p.riemann_sample_in_bounds, &[a, c, m_ac, i, hac, hi]);
        let a_le_spac_ty = cle(d, p, a, sp_ac);
        let spac_le_c_ty = cle(d, p, sp_ac, c);
        let a_le_spac = d.const_app(logic.and_left, &[a_le_spac_ty, spac_le_c_ty, and_ac]);
        let spac_le_c = d.const_app(logic.and_right, &[a_le_spac_ty, spac_le_c_ty, and_ac]);
        let spac_le_b = d.lemma(p.le_trans, &[sp_ac, c, b, spac_le_c, hcb]);

        // h_sp : Equiv sp_ab sp_ac -- IDENTICAL to
        // `declare_riemann_sum_split_exact`'s own `pointwise1`.
        let symm_ac1 = d.lemma(p.equiv_symm, &[delta_ac, delta_ab, h_delta_ac]);
        let refl_oi = d.lemma(p.equiv_refl, &[oi]);
        let mc = d.lemma(
            p.mul_congr,
            &[oi, oi, delta_ab, delta_ac, refl_oi, symm_ac1],
        );
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        let oi_delta_ab = cmul(d, p, oi, delta_ab);
        let oi_delta_ac = cmul(d, p, oi, delta_ac);
        let h_sp = d.lemma(p.add_congr, &[a, a, oi_delta_ab, oi_delta_ac, refl_a, mc]);

        let f_spab = d.apply(f, &[sp_ab]);
        let f_spac = d.apply(f, &[sp_ac]);
        let hcong_i = d.lemma(
            p.congr_of_uniformly_continuous,
            &[
                f, a, b, u, sp_ab, sp_ac, a_le_spab, spab_le_b, a_le_spac, spac_le_b, h_sp,
            ],
        );
        let symm_ac2 = d.lemma(p.equiv_symm, &[delta_ac, delta_ab, h_delta_ac]);
        let final_i = d.lemma(
            p.mul_congr,
            &[f_spab, f_spac, delta_ab, delta_ac, hcong_i, symm_ac2],
        );

        let inner = d.lam_fv(hi_fv, hi_ty, final_i);
        d.lam_fv(i_fv, nat, inner)
    };
    let piece1 = {
        let proof_fn = sum_range_congr_lt_proof(d, p, f_ab, f_ac, n_ac);
        d.apply(proof_fn, &[bounded_pointwise1])
    };

    // --- piece 2 : Equiv (sumRange (shifted n_ac f_ab) n_cb) (riemannSum F c
    // b m_cb) --- BOUNDED pointwise (k < n_cb).
    let f_cb = summand_fn(d, p, f, c, delta_cb);
    let f_ab_shifted = shifted_fn(d, n_ac, f_ab);
    let bounded_pointwise2 = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_ty = d.lt(k, n_cb);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);

        let ok = d.const_app(p.of_nat, &[k]);
        let nack = NatOps::add(d, n_ac, k);
        let onack = d.const_app(p.of_nat, &[nack]);
        let sp_shift = sample_point(d, p, a, delta_ab, nack);
        let sp_cb = sample_point(d, p, c, delta_cb, k);

        // sp_shift in [a, b]: `n_ac + k < n_ac + n_cb`, defeq `succ m_ab`
        // (`Nat.add` recurses on its right argument, and `n_cb` is literally
        // `Nat.succ m_cb`), via `add_lt_add_left`.
        let np = d.prelude();
        let hk_full = d.lemma(np.add_lt_add_left, &[n_ac, k, n_cb, hk]);
        let and_shift = d.lemma(
            p.riemann_sample_in_bounds,
            &[a, b, m_ab, nack, hab, hk_full],
        );
        let a_le_spshift_ty = cle(d, p, a, sp_shift);
        let spshift_le_b_ty = cle(d, p, sp_shift, b);
        let a_le_spshift = d.const_app(
            logic.and_left,
            &[a_le_spshift_ty, spshift_le_b_ty, and_shift],
        );
        let spshift_le_b = d.const_app(
            logic.and_right,
            &[a_le_spshift_ty, spshift_le_b_ty, and_shift],
        );

        // sp_cb in [a, b]: directly in [c, b] via `riemann_sample_in_bounds`
        // at the EXACT bound `k < n_cb`, then `a <= c` (`hac`) extends the
        // lower bound.
        let and_cb = d.lemma(p.riemann_sample_in_bounds, &[c, b, m_cb, k, hcb, hk]);
        let c_le_spcb_ty = cle(d, p, c, sp_cb);
        let spcb_le_b_ty = cle(d, p, sp_cb, b);
        let c_le_spcb = d.const_app(logic.and_left, &[c_le_spcb_ty, spcb_le_b_ty, and_cb]);
        let spcb_le_b = d.const_app(logic.and_right, &[c_le_spcb_ty, spcb_le_b_ty, and_cb]);
        let a_le_spcb = d.lemma(p.le_trans, &[a, c, sp_cb, hac, c_le_spcb]);

        // h_sp2 : Equiv sp_shift sp_cb -- IDENTICAL to
        // `declare_riemann_sum_split_exact`'s own `pointwise2`.
        let of_nat_add_step = d.lemma(p.of_nat_add, &[n_ac, k]); // Equiv onack (add on_ac ok)
        let sum_on2 = cadd(d, p, on_ac, ok);
        let refl_delta_ab2 = d.lemma(p.equiv_refl, &[delta_ab]);
        let mul_onack_delta = cmul(d, p, onack, delta_ab);
        let mul_sumon2_delta = cmul(d, p, sum_on2, delta_ab);
        let step_m1 = d.lemma(
            p.mul_congr,
            &[
                onack,
                sum_on2,
                delta_ab,
                delta_ab,
                of_nat_add_step,
                refl_delta_ab2,
            ],
        );

        let ok_delta_ab = cmul(d, p, ok, delta_ab);
        let add_w1_okdab = cadd(d, p, w1, ok_delta_ab);
        let step_rd = right_distrib(d, p, on_ac, ok, delta_ab); // Equiv mul_sumon2_delta add_w1_okdab

        let chain_inner = echain(
            d,
            p,
            mul_onack_delta,
            &[(mul_sumon2_delta, step_m1), (add_w1_okdab, step_rd)],
        );

        let a_add_w1_okdab = cadd(d, p, a, add_w1_okdab);
        let refl_a2 = d.lemma(p.equiv_refl, &[a]);
        let step_outer = d.lemma(
            p.add_congr,
            &[a, a, mul_onack_delta, add_w1_okdab, refl_a2, chain_inner],
        );

        let c_add_okdab = cadd(d, p, c, ok_delta_ab);
        let assoc3 = d.lemma(p.add_assoc, &[a, w1, ok_delta_ab]); // Equiv c_add_okdab a_add_w1_okdab
        let assoc3_symm = d.lemma(p.equiv_symm, &[c_add_okdab, a_add_w1_okdab, assoc3]);

        let symm_cb1 = d.lemma(p.equiv_symm, &[delta_cb, delta_ab, h_delta_cb]);
        let refl_ok = d.lemma(p.equiv_refl, &[ok]);
        let step_okdelta = d.lemma(
            p.mul_congr,
            &[ok, ok, delta_ab, delta_cb, refl_ok, symm_cb1],
        );
        let ok_delta_cb = cmul(d, p, ok, delta_cb);
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        let step_final_inner = d.lemma(
            p.add_congr,
            &[c, c, ok_delta_ab, ok_delta_cb, refl_c, step_okdelta],
        );

        let h_sp2 = echain(
            d,
            p,
            sp_shift,
            &[
                (a_add_w1_okdab, step_outer),
                (c_add_okdab, assoc3_symm),
                (sp_cb, step_final_inner),
            ],
        );

        let f_spshift = d.apply(f, &[sp_shift]);
        let f_spcb = d.apply(f, &[sp_cb]);
        let hcong_k = d.lemma(
            p.congr_of_uniformly_continuous,
            &[
                f,
                a,
                b,
                u,
                sp_shift,
                sp_cb,
                a_le_spshift,
                spshift_le_b,
                a_le_spcb,
                spcb_le_b,
                h_sp2,
            ],
        );
        let symm_cb2 = d.lemma(p.equiv_symm, &[delta_cb, delta_ab, h_delta_cb]);
        let final_k = d.lemma(
            p.mul_congr,
            &[f_spshift, f_spcb, delta_ab, delta_cb, hcong_k, symm_cb2],
        );

        let inner = d.lam_fv(hk_fv, hk_ty, final_k);
        d.lam_fv(k_fv, nat, inner)
    };
    let piece2 = {
        let proof_fn = sum_range_congr_lt_proof(d, p, f_ab_shifted, f_cb, n_cb);
        d.apply(proof_fn, &[bounded_pointwise2])
    };

    // --- assemble --- IDENTICAL to `declare_riemann_sum_split_exact`.
    let split = d.lemma(p.sum_range_split, &[f_ab, n_ac, n_cb]);
    let sum_f_ab_nac = d.const_app(p.sum_range, &[f_ab, n_ac]);
    let sum_shifted_ncb = d.const_app(p.sum_range, &[f_ab_shifted, n_cb]);
    let riemann_ac = rsum(d, p, f, a, c, m_ac);
    let riemann_cb = rsum(d, p, f, c, b, m_cb);
    let combine = d.lemma(
        p.add_congr,
        &[
            sum_f_ab_nac,
            riemann_ac,
            sum_shifted_ncb,
            riemann_cb,
            piece1,
            piece2,
        ],
    );

    let sum_split_domain = NatOps::add(d, n_ac, n_cb);
    let sumrange_full = d.const_app(p.sum_range, &[f_ab, sum_split_domain]);
    let combined_rhs = cadd(d, p, sum_f_ab_nac, sum_shifted_ncb);
    let target_rhs = cadd(d, p, riemann_ac, riemann_cb);
    let proof = d.lemma(
        p.equiv_trans,
        &[sumrange_full, combined_rhs, target_rhs, split, combine],
    );

    let ty = {
        let lhs = rsum(d, p, f, a, b, m_ab);
        let concl = equiv(d, p, lhs, target_rhs);
        let after_hab = d.arrow(hab_ty, concl);
        let after_u = d.arrow(u_ty, after_hab);
        let over_mcb = d.pi_fv(mcb_fv, nat, after_u);
        let over_mac = d.pi_fv(mac_fv, nat, over_mcb);
        let over_b = d.pi_fv(b_fv, carrier, over_mac);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_hab = d.lam_fv(hab_fv, hab_ty, proof);
        let with_u = d.lam_fv(u_fv, u_ty, with_hab);
        let over_mcb = d.lam_fv(mcb_fv, nat, with_u);
        let over_mac = d.lam_fv(mac_fv, nat, over_mcb);
        let over_b = d.lam_fv(b_fv, carrier, over_mac);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_split_exact_of_uc,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `CReal.integral_split`, the SEVENTEENTH lane: one leg's `Converges`
// fact at an ARBITRARY mesh family ------------------------------------------
//
// The TWELFTH lane's sizing routed the combine through
// `close_within_of_within_indexed` + `abs_add_le` twice +
// `equiv_zero_of_small`. This lane takes a shorter route that needs none of
// those three: [`declare_integral_add`] and [`declare_integral_le`] both show
// that once every leg is a `Converges` fact at a mesh family the caller
// chooses, the combine is `converges_add` + `converges_of_close` +
// `converges_unique`, and no `abs` estimate is done by hand at all.
//
// [`leg_converges`] is that per-leg step, and it is where the whole estimate
// lives. It is `declare_integral_le`'s own `step_f`/`step_g` construction with
// ONE generalization: that declaration reaches only the specific refinement
// `common_refinement(m1, m2)`, whereas an `integral_split` leg must reach
// whatever mesh count [`mesh_count_align_mul`] hands it. The generalization is
// [`CRealPrelude::riemann_sum_shared_accuracy_close`] at a FREE `k1`
// (`declare_integral_le` calls `riemann_sum_cauchy` directly, which fixes the
// refinement), plus one inequality `declare_integral_le` never needs:
//
// ```text
// natDivSucc 1 l  ≤  natDivSucc 1 n      [Rat.natDivSucc_antitone, needs n ≤ l]
// ```
//
// `riemann_sum_shared_accuracy_close`'s bound carries `modulus(l, shift jj1)`
// where `l := common_refinement(m1, m2).0` is its internal shared refinement,
// while [`bnd_leg_plus_share_le`] folds only the all-at-one-index shape
// `modulus(idx, shift idx)`. With `oi = oj = jj1 = jj2 := n` the two differ in
// exactly that one leaf, and `Nat.le n l` closes the gap:
// `l = succ_mul_succ(m2, m1).0 = ((m2·m1) + m2) + m1 ≥ m1` ([`nat_le_add_left`]),
// so the caller's own `Nat.le n (M n)` suffices. That is why this helper takes
// `idx_le` as well as `deep_le`.

/// Build `Converges (fun n => riemannSum F x y (M n)) (CReal.integral F x y
/// hxy uxy)` for ANY mesh family `M` at least as fine as the native modulus
/// and at least as deep as the accuracy index itself.
///
/// `mesh(d, n)` builds `M n`; `deep_le(d, n)` proves
/// `Nat.le (deep_at(F, x, y, uxy, n)) (M n)`; `idx_le(d, n)` proves
/// `Nat.le n (M n)`. All three are called at ONE shared symbolic `n`, so what
/// they return may mention it freely — but nothing they return may mention the
/// `Nat.le_dest` depth, which does not exist yet when they run.
///
/// Returns `(seq, proof)`, `seq := fun n => riemannSum F x y (M n)`.
#[allow(clippy::too_many_arguments)]
fn leg_converges(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    x: ExprId,
    y: ExprId,
    hxy: ExprId,
    uxy: ExprId,
    mesh: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    deep_le: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    idx_le: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let rat = p.rat;

    let (f_lambda, _k_native, _cauchy) = integral_witness(d, p, f, x, y, hxy, uxy);
    let integral_val = d.const_app(p.integral, &[f, x, y, hxy, uxy]);
    let conv_native = d.lemma(p.integral_converges, &[f, x, y, hxy, uxy]);

    let width = width_of(d, p, x, y);
    let (_c0, magnitude, _width_le_mag) = direct_bound_le(d, p, width);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let m_n = mesh(d, n);
    let deep = deep_at(d, p, f, x, y, uxy, n);
    let zero = d.num(0);
    let m2 = NatOps::add(d, deep, zero);

    let shift_n = shift(d, n);
    let m_n_sn = modulus(d, p, n, shift_n);
    let m_sn_n = modulus(d, p, shift_n, n);
    let a1_n = div_succ(d, p, 1, n);
    let a2 = div_succ(d, p, 1, shift_n);

    // `k` is a deterministic function of `magnitude` and the index ALONE
    // (never of `m` or `bound_at_idx` -- see `bnd_leg_plus_share_le`'s own
    // doc comment), so this OUTER call returns the same `ExprId` the two calls
    // inside the `le_dest_elim` continuation do. It has to be available out
    // here: `target` may not mention the bound depth, and `kc` is built from
    // `k`.
    let bound2_fn = shared_accuracy_bound_fn(d, p, x, y, n, m2);
    let b2n = d.apply(bound2_fn, &[n]);
    let (k, leg2_le) = bnd_leg_plus_share_le(d, p, x, y, n, m2, magnitude, b2n);
    let k_n = nds(d, p, k, n);
    let (kc, eq_fuse) = fuse_nds(d, p, k, k, n);
    let kc_n = nds(d, p, kc, n);

    let seq_g = rsum(d, p, f, x, y, m_n);
    let seq_native = rsum(d, p, f, x, y, m2);
    let sg = sample(d, p, seq_g, n);
    let sf = sample(d, p, seq_native, n);
    let diff_target = rsub(d, rat, sg, sf);
    let target = within(d, p, diff_target, kc_n);

    let hle = deep_le(d, n);
    let hn = idx_le(d, n);

    let per_n = le_dest_elim(d, deep, m_n, hle, target, &|d, depth, eq| {
        // `m1` is `riemann_sum_shared_accuracy_close`'s own `deep + k1` at
        // `k1 := depth`, so `raw` is stated about `rsum(m1)` and only the
        // final `nat_rewrite_prop` moves it onto `M n`.
        let m1 = NatOps::add(d, deep, depth);
        let (l, _l2, _l2_eq_l) = common_refinement(d, m1, m2);

        let raw = d.lemma(
            p.riemann_sum_shared_accuracy_close,
            &[f, x, y, n, depth, zero, hxy, uxy, n, n, n, n],
        );

        // `raw`'s bound, reconstructed term-for-term from
        // `shared_accuracy_close_at_proof` at `oi = oj = jj1 = jj2 = n`.
        let m_l_sn = modulus(d, p, l, shift_n);
        let bound1_fn = shared_accuracy_bound_fn(d, p, x, y, n, m1);
        let b1n = d.apply(bound1_fn, &[n]);
        let bnd1 = {
            let inner = radd(d, m_l_sn, b1n);
            radd(d, inner, m_sn_n)
        };
        let bnd2 = {
            let inner = radd(d, m_l_sn, b2n);
            radd(d, inner, m_sn_n)
        };
        let total = radd(d, bnd1, bnd2);

        // --- `Nat.le n l`, the one step `declare_integral_le` never needs.
        let hn_m1 = {
            let eq_symm = d.symm(m1, m_n, eq); // Eq Nat (M n) m1
            nat_rewrite_prop(d, m_n, m1, eq_symm, hn, &|d, t| d.le(n, t))
        };
        let np = d.prelude();
        let head = {
            let mm = NatOps::mul(d, m2, m1);
            d.const_app(np.add, &[mm, m2])
        };
        let m1_le_l = nat_le_add_left(d, head, m1);
        let n_le_l = d.lemma(np.le_trans, &[n, m1, l, hn_m1, m1_le_l]);
        let anti = d.lemma(rat.nat_div_succ_antitone, &[n, l, n_le_l]);
        let a1_l = div_succ(d, p, 1, l);
        let refl_a2 = d.lemma(rat.le_refl, &[a2]);
        // mod_le : modulus(l, shift n) ≤ modulus(n, shift n).
        let mod_le = d.lemma(rat.add_le_add, &[a1_l, a1_n, a2, a2, anti, refl_a2]);

        let refl_msn = d.lemma(rat.le_refl, &[m_sn_n]);

        let refl_b1 = d.lemma(rat.le_refl, &[b1n]);
        let inner1_actual = radd(d, m_l_sn, b1n);
        let inner1_target = radd(d, m_n_sn, b1n);
        let inner1_le = d.lemma(rat.add_le_add, &[m_l_sn, m_n_sn, b1n, b1n, mod_le, refl_b1]);
        let bnd1_target = radd(d, inner1_target, m_sn_n);
        let bnd1_le_t = d.lemma(
            rat.add_le_add,
            &[
                inner1_actual,
                inner1_target,
                m_sn_n,
                m_sn_n,
                inner1_le,
                refl_msn,
            ],
        );

        let refl_b2 = d.lemma(rat.le_refl, &[b2n]);
        let inner2_actual = radd(d, m_l_sn, b2n);
        let inner2_target = radd(d, m_n_sn, b2n);
        let inner2_le = d.lemma(rat.add_le_add, &[m_l_sn, m_n_sn, b2n, b2n, mod_le, refl_b2]);
        let bnd2_target = radd(d, inner2_target, m_sn_n);
        let bnd2_le_t = d.lemma(
            rat.add_le_add,
            &[
                inner2_actual,
                inner2_target,
                m_sn_n,
                m_sn_n,
                inner2_le,
                refl_msn,
            ],
        );

        // --- fold each standard-shaped leg into `natDivSucc(k, n)`, dropping
        // the extra `+natDivSucc(1,n)` share exactly the way
        // `declare_integral_le` does (no partner leg to absorb it into).
        let (_k1, leg1_le) = bnd_leg_plus_share_le(d, p, x, y, n, m1, magnitude, b1n);
        let one_nat = d.num(1);
        let a1_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, n]);

        let t1_le_extra = le_add_nonneg_right(d, p, bnd1_target, a1_n, a1_nonneg);
        let t1_extra = radd(d, bnd1_target, a1_n);
        let t1_le_k = d.lemma(
            rat.le_trans,
            &[bnd1_target, t1_extra, k_n, t1_le_extra, leg1_le],
        );
        let bnd1_le_k = d.lemma(rat.le_trans, &[bnd1, bnd1_target, k_n, bnd1_le_t, t1_le_k]);

        let t2_le_extra = le_add_nonneg_right(d, p, bnd2_target, a1_n, a1_nonneg);
        let t2_extra = radd(d, bnd2_target, a1_n);
        let t2_le_k = d.lemma(
            rat.le_trans,
            &[bnd2_target, t2_extra, k_n, t2_le_extra, leg2_le],
        );
        let bnd2_le_k = d.lemma(rat.le_trans, &[bnd2, bnd2_target, k_n, bnd2_le_t, t2_le_k]);

        let sum_k = radd(d, k_n, k_n);
        let total_le_sum = d.lemma(
            rat.add_le_add,
            &[bnd1, k_n, bnd2, k_n, bnd1_le_k, bnd2_le_k],
        );
        let total_le_kc = rat_eq_rewrite(d, sum_k, kc_n, eq_fuse, total_le_sum, &|d, t| {
            rle(d, rat, total, t)
        });

        let rsum_m1 = rsum(d, p, f, x, y, m1);
        let s1 = sample(d, p, rsum_m1, n);
        let diff1 = rsub(d, rat, s1, sf);
        let weakened = weaken(d, p, diff1, total, kc_n, raw, total_le_kc);

        nat_rewrite_prop(d, m1, m_n, eq, weakened, &|d, t| {
            let rs = rsum(d, p, f, x, y, t);
            let s = sample(d, p, rs, n);
            let df = rsub(d, rat, s, sf);
            within(d, p, df, kc_n)
        })
    });

    let cross = d.lam_fv(n_fv, nat, per_n);
    let new_seq = d.lam_fv(n_fv, nat, seq_g);

    let proof = d.lemma(
        p.converges_of_close,
        &[f_lambda, new_seq, integral_val, kc, cross, conv_native],
    );
    (new_seq, proof)
}

#[cfg(test)]
mod leg_converges_tests {
    use super::*;
    use crate::Declaration;

    /// Symbolic in `F`, `a`, `b`, the order proof and the continuity witness,
    /// at the mesh family `M n := deep(n) + n` — the simplest family that is
    /// genuinely NEITHER the native one (`deep(n) + 0`, which
    /// `integral_converges` already covers) NOR reachable by
    /// `declare_integral_le`'s `common_refinement`, and which exercises both
    /// callbacks: `deep_le` is `Nat.le_add_right` and `idx_le` is
    /// [`nat_le_add_left`], the two opposite sides of one `Nat.add`.
    #[test]
    fn leg_converges_proves_convergence_at_a_padded_mesh_family() {
        crate::on_a_deep_stack(leg_converges_padded_body);
    }

    fn leg_converges_padded_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);
        let f_ty = fn_ty(&mut d, p);

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let hab_ty = cle(&mut d, p, a, b);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);
        let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);

        let (seq, proof) = leg_converges(
            &mut d,
            p,
            f,
            a,
            b,
            hab,
            u,
            &|d, n| {
                let deep = deep_at(d, p, f, a, b, u, n);
                NatOps::add(d, deep, n)
            },
            &|d, n| {
                let deep = deep_at(d, p, f, a, b, u, n);
                let np = d.prelude();
                d.lemma(np.le_add_right, &[deep, n])
            },
            &|d, n| {
                let deep = deep_at(d, p, f, a, b, u, n);
                nat_le_add_left(d, deep, n)
            },
        );

        // Non-vacuity: the sequence must be the PADDED family, not the native
        // one `integral_converges` already gives for free.
        let native = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let deep = deep_at(&mut d, p, f, a, b, u, n);
            let zero = d.num(0);
            let m = NatOps::add(&mut d, deep, zero);
            let rs = rsum(&mut d, p, f, a, b, m);
            let nat = d.nat_ty();
            d.lam_fv(n_fv, nat, rs)
        };
        assert_ne!(
            seq, native,
            "leg_converges must land on the caller's mesh family, not the native one"
        );

        let integral_val = d.const_app(p.integral, &[f, a, b, hab, u]);
        let concl = converges_applied(&mut d, p, seq, integral_val);

        let ty = {
            let t = d.pi_fv(u_fv, u_ty, concl);
            let t = d.pi_fv(hab_fv, hab_ty, t);
            let t = d.pi_fv(b_fv, carrier, t);
            let t = d.pi_fv(a_fv, carrier, t);
            d.pi_fv(f_fv, f_ty, t)
        };
        let value = {
            let v = d.lam_fv(u_fv, u_ty, proof);
            let v = d.lam_fv(hab_fv, hab_ty, v);
            let v = d.lam_fv(b_fv, carrier, v);
            let v = d.lam_fv(a_fv, carrier, v);
            d.lam_fv(f_fv, f_ty, v)
        };

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "legConvergesPaddedSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "leg_converges must prove Converges at a padded mesh family: {:?}",
            result.err()
        );
    }
}

// --- `CReal.integral_split` -- the assembly ---------------------------------
//
// Every piece is now a `Converges` fact, so the combine has no rational
// estimate in it at all:
//
// ```text
// conv_ab  : Converges (fun n => riemannSum F a b (combined n)) (integral F a b hab u)
// conv_ac  : Converges (fun n => riemannSum F a c (m_ac   n)) (integral F a c hac uac)
// conv_cb  : Converges (fun n => riemannSum F c b (m_cb   n)) (integral F c b hcb ucb)
//   [leg_converges, three times]
// conv_sum : Converges (fun n => add (g_ac n) (g_cb n)) (add I_ac I_cb)
//   [converges_add]
// cross    : ∀ n, Within (seq (g_ab n) n − seq (sum_seq n) n) (natDivSucc 2 n)
//   [split_identity_at_equiv_point at (m_ac n, m_cb n), APPLIED at n -- `Equiv`
//    unfolds to exactly this per-index `Within` at bound `2/(n+1)`, which is
//    the same step `declare_converges_of_equiv` takes]
// step     : Converges g_ab (add I_ac I_cb)      [converges_of_close at Kc := 2]
// final    : Equiv I_ab (add I_ac I_cb)          [converges_unique]
// ```
//
// `c` is NOT universally quantified: it is the base split point `c_0` of the
// caller's rational proportion `(m_ac0, m_cb0)`, because
// [`CRealPrelude::riemann_sum_split_scale_invariant`] proves `Equiv c_k c_0`
// for that family and for no other — the SIXTEENTH lane's Gap B entry says so
// in as many words. `big_n` is likewise not free: `leg_converges` needs
// `Nat.le n (M n)` on every leg, so `big_n := n`.

/// `c_0 := a + ofNat(succ m_ac0) · delta_of(a, b, succ m_ac0 + m_cb0)` — the
/// base split point of the rational proportion `succ m_ac0 : succ m_cb0`,
/// built with the identical `delta_of`/`of_nat`/`cmul`/`cadd` recipe
/// [`declare_riemann_sum_split_scale_invariant`]'s own `c_0` uses, so the two
/// intern to the SAME `ExprId` and its `Equiv c_k c_0` applies on the nose.
fn split_point_base(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    m_ac0: ExprId,
    m_cb0: ExprId,
) -> ExprId {
    let n_ac0 = d.succ(m_ac0);
    let m_ab0 = NatOps::add(d, n_ac0, m_cb0);
    let delta_ab0 = delta_of(d, p, a, b, m_ab0);
    let on_ac0 = d.const_app(p.of_nat, &[n_ac0]);
    let w = cmul(d, p, on_ac0, delta_ab0);
    cadd(d, p, a, w)
}

/// [`mesh_count_align_mul_bounds`] at the three moduli this split needs, with
/// `big_n := n`. Called once per `leg_converges` callback and once for the
/// cross bound; hash-consing makes every call return the same `ExprId`s.
#[allow(clippy::too_many_arguments)]
fn split_mesh_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    u: ExprId,
    uac: ExprId,
    ucb: ExprId,
    m_ac0: ExprId,
    m_cb0: ExprId,
    n: ExprId,
) -> MeshAlignMulBounds {
    let deep_ab = deep_at(d, p, f, a, b, u, n);
    let deep_ac = deep_at(d, p, f, a, c, uac, n);
    let deep_cb = deep_at(d, p, f, c, b, ucb, n);
    mesh_count_align_mul_bounds(d, deep_ab, deep_ac, deep_cb, m_ac0, m_cb0, n)
}

/// `Equiv (integral F a b hab u) (add (integral F a c hac uac) (integral F c b
/// hcb ucb))` at `c := ` [`split_point_base`]`(a, b, m_ac0, m_cb0)`.
///
/// Shared by [`declare_integral_split`] and its own symbolic test so the two
/// cannot drift.
#[allow(clippy::too_many_arguments)]
fn integral_split_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    m_ac0: ExprId,
    m_cb0: ExprId,
    hab: ExprId,
    u: ExprId,
    hac: ExprId,
    hcb: ExprId,
    uac: ExprId,
    ucb: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let c = split_point_base(d, p, a, b, m_ac0, m_cb0);

    let integral_ab = d.const_app(p.integral, &[f, a, b, hab, u]);
    let integral_ac = d.const_app(p.integral, &[f, a, c, hac, uac]);
    let integral_cb = d.const_app(p.integral, &[f, c, b, hcb, ucb]);

    let (g_ab, conv_ab) = leg_converges(
        d,
        p,
        f,
        a,
        b,
        hab,
        u,
        &|d, n| split_mesh_bounds(d, p, f, a, b, c, u, uac, ucb, m_ac0, m_cb0, n).combined,
        &|d, n| split_mesh_bounds(d, p, f, a, b, c, u, uac, ucb, m_ac0, m_cb0, n).hle_ab,
        &|d, n| split_mesh_bounds(d, p, f, a, b, c, u, uac, ucb, m_ac0, m_cb0, n).hn_ab,
    );
    let (g_ac, conv_ac) = leg_converges(
        d,
        p,
        f,
        a,
        c,
        hac,
        uac,
        &|d, n| split_mesh_bounds(d, p, f, a, b, c, u, uac, ucb, m_ac0, m_cb0, n).m_ac,
        &|d, n| split_mesh_bounds(d, p, f, a, b, c, u, uac, ucb, m_ac0, m_cb0, n).hle_ac,
        &|d, n| split_mesh_bounds(d, p, f, a, b, c, u, uac, ucb, m_ac0, m_cb0, n).hn_ac,
    );
    let (g_cb, conv_cb) = leg_converges(
        d,
        p,
        f,
        c,
        b,
        hcb,
        ucb,
        &|d, n| split_mesh_bounds(d, p, f, a, b, c, u, uac, ucb, m_ac0, m_cb0, n).m_cb,
        &|d, n| split_mesh_bounds(d, p, f, a, b, c, u, uac, ucb, m_ac0, m_cb0, n).hle_cb,
        &|d, n| split_mesh_bounds(d, p, f, a, b, c, u, uac, ucb, m_ac0, m_cb0, n).hn_cb,
    );

    let sum_target = cadd(d, p, integral_ac, integral_cb);
    let conv_sum = d.lemma(
        p.converges_add,
        &[g_ac, g_cb, integral_ac, integral_cb, conv_ac, conv_cb],
    );
    let sum_seq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let ga = d.apply(g_ac, &[n]);
        let gb = d.apply(g_cb, &[n]);
        let added = cadd(d, p, ga, gb);
        d.lam_fv(n_fv, nat, added)
    };

    // --- the per-index cross bound. `Equiv` IS the `2/(n+1)` per-index
    // `Within`, so the split identity applied at `n` is already the shape
    // `converges_of_close` takes -- the same step `declare_converges_of_equiv`
    // makes, and the reason no `abs_add_le`/`equiv_zero_of_small` appears in
    // this construction.
    let cross = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let mb = split_mesh_bounds(d, p, f, a, b, c, u, uac, ucb, m_ac0, m_cb0, n);

        // hc : Equiv c_k c, at THIS accuracy's own scale factor.
        let hc = d.lemma(
            p.riemann_sum_split_scale_invariant,
            &[a, b, m_ac0, m_cb0, mb.k],
        );
        let c_k = {
            let n_ac = d.succ(mb.m_ac);
            let delta_ab = delta_of(d, p, a, b, mb.combined);
            let on_ac = d.const_app(p.of_nat, &[n_ac]);
            let w1 = cmul(d, p, on_ac, delta_ab);
            cadd(d, p, a, w1)
        };
        let hc_symm = d.lemma(p.equiv_symm, &[c_k, c, hc]); // Equiv c c_k

        // The caller's order proofs transported onto `c_k`. `le_congr`'s
        // `Equiv` arguments run OLD -> NEW and its `le` premise is the
        // PRE-substitution one, the shape `declare_riemann_sum_split_exact_of_uc`
        // already uses for its own `hcb`.
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        let refl_b = d.lemma(p.equiv_refl, &[b]);
        let hac_k = d.lemma(p.le_congr, &[a, a, c, c_k, refl_a, hc_symm, hac]);
        let hc_kb = d.lemma(p.le_congr, &[c, c_k, b, b, hc_symm, refl_b, hcb]);

        let split_id = split_identity_at_equiv_point(
            d, p, f, a, b, u, hab, mb.m_ac, mb.m_cb, c, hac_k, hc_kb, hac, hcb, hc,
        );
        let inst = d.apply(split_id, &[n]);
        d.lam_fv(n_fv, nat, inst)
    };

    let two_nat = d.num(2);
    let step = d.lemma(
        p.converges_of_close,
        &[sum_seq, g_ab, sum_target, two_nat, cross, conv_sum],
    );
    d.lemma(
        p.converges_unique,
        &[g_ab, integral_ab, sum_target, conv_ab, step],
    )
}

/// Admit `CReal.integral_split`. See this section's own module documentation
/// for the route and for why `c` is the base split point rather than a free
/// `CReal`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_integral_split(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let mac0_fv = d.fresh_fvar();
    let m_ac0 = d.kernel().fvar(mac0_fv);
    let mcb0_fv = d.fresh_fvar();
    let m_cb0 = d.kernel().fvar(mcb0_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let c = split_point_base(d, p, a, b, m_ac0, m_cb0);

    let hac_ty = cle(d, p, a, c);
    let hac_fv = d.fresh_fvar();
    let hac = d.kernel().fvar(hac_fv);
    let hcb_ty = cle(d, p, c, b);
    let hcb_fv = d.fresh_fvar();
    let hcb = d.kernel().fvar(hcb_fv);
    let uac_ty = d.const_app(p.uniformly_continuous_on, &[f, a, c]);
    let uac_fv = d.fresh_fvar();
    let uac = d.kernel().fvar(uac_fv);
    let ucb_ty = d.const_app(p.uniformly_continuous_on, &[f, c, b]);
    let ucb_fv = d.fresh_fvar();
    let ucb = d.kernel().fvar(ucb_fv);

    let proof = integral_split_proof(d, p, f, a, b, m_ac0, m_cb0, hab, u, hac, hcb, uac, ucb);

    let integral_ab = d.const_app(p.integral, &[f, a, b, hab, u]);
    let integral_ac = d.const_app(p.integral, &[f, a, c, hac, uac]);
    let integral_cb = d.const_app(p.integral, &[f, c, b, hcb, ucb]);
    let rhs = cadd(d, p, integral_ac, integral_cb);
    let concl = equiv(d, p, integral_ab, rhs);

    // `concl` mentions every hypothesis (through the three `integral`
    // applications), so ALL of them bind with `pi_fv`, never `d.arrow` -- the
    // trap `declare_integral_const`'s own doc comment names.
    let ty = {
        let t = d.pi_fv(ucb_fv, ucb_ty, concl);
        let t = d.pi_fv(uac_fv, uac_ty, t);
        let t = d.pi_fv(hcb_fv, hcb_ty, t);
        let t = d.pi_fv(hac_fv, hac_ty, t);
        let t = d.pi_fv(u_fv, u_ty, t);
        let t = d.pi_fv(hab_fv, hab_ty, t);
        let t = d.pi_fv(mcb0_fv, nat, t);
        let t = d.pi_fv(mac0_fv, nat, t);
        let t = d.pi_fv(b_fv, carrier, t);
        let t = d.pi_fv(a_fv, carrier, t);
        d.pi_fv(f_fv, f_ty, t)
    };
    let value = {
        let v = d.lam_fv(ucb_fv, ucb_ty, proof);
        let v = d.lam_fv(uac_fv, uac_ty, v);
        let v = d.lam_fv(hcb_fv, hcb_ty, v);
        let v = d.lam_fv(hac_fv, hac_ty, v);
        let v = d.lam_fv(u_fv, u_ty, v);
        let v = d.lam_fv(hab_fv, hab_ty, v);
        let v = d.lam_fv(mcb0_fv, nat, v);
        let v = d.lam_fv(mac0_fv, nat, v);
        let v = d.lam_fv(b_fv, carrier, v);
        let v = d.lam_fv(a_fv, carrier, v);
        d.lam_fv(f_fv, f_ty, v)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.integral_split,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod integral_split_tests {
    use super::*;
    use crate::Declaration;

    /// Symbolic in `F`, `a`, `b`, the proportion `(m_ac0, m_cb0)`, all three
    /// continuity witnesses and all three order proofs — closed into a real
    /// `Theorem`. This is what consumes `mesh_count_align_mul_bounds`,
    /// `leg_converges`, `split_identity_at_equiv_point`,
    /// `riemann_sum_split_scale_invariant` and `riemann_sum_congr_endpoints`
    /// at once.
    #[test]
    fn integral_split_proves_additivity_at_the_base_split_point() {
        crate::on_a_deep_stack(integral_split_body);
    }

    fn integral_split_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);
        let nat = d.nat_ty();
        let f_ty = fn_ty(&mut d, p);

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let mac0_fv = d.fresh_fvar();
        let m_ac0 = d.kernel().fvar(mac0_fv);
        let mcb0_fv = d.fresh_fvar();
        let m_cb0 = d.kernel().fvar(mcb0_fv);

        let hab_ty = cle(&mut d, p, a, b);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);
        let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);

        let c = split_point_base(&mut d, p, a, b, m_ac0, m_cb0);

        // Non-vacuity, aimed at the FIFTEENTH lane's worry that the reachable
        // stratum is bisection-only: the split point must genuinely depend on
        // the proportion, so transposing it must give a DIFFERENT `CReal`.
        let c_transposed = split_point_base(&mut d, p, a, b, m_cb0, m_ac0);
        assert_ne!(
            c, c_transposed,
            "the split point must depend on the proportion, not be the midpoint"
        );

        let hac_ty = cle(&mut d, p, a, c);
        let hac_fv = d.fresh_fvar();
        let hac = d.kernel().fvar(hac_fv);
        let hcb_ty = cle(&mut d, p, c, b);
        let hcb_fv = d.fresh_fvar();
        let hcb = d.kernel().fvar(hcb_fv);
        let uac_ty = d.const_app(p.uniformly_continuous_on, &[f, a, c]);
        let uac_fv = d.fresh_fvar();
        let uac = d.kernel().fvar(uac_fv);
        let ucb_ty = d.const_app(p.uniformly_continuous_on, &[f, c, b]);
        let ucb_fv = d.fresh_fvar();
        let ucb = d.kernel().fvar(ucb_fv);

        let proof =
            integral_split_proof(&mut d, p, f, a, b, m_ac0, m_cb0, hab, u, hac, hcb, uac, ucb);

        let integral_ab = d.const_app(p.integral, &[f, a, b, hab, u]);
        let integral_ac = d.const_app(p.integral, &[f, a, c, hac, uac]);
        let integral_cb = d.const_app(p.integral, &[f, c, b, hcb, ucb]);
        let rhs = cadd(&mut d, p, integral_ac, integral_cb);
        assert_ne!(
            integral_ab, rhs,
            "the two sides must be different terms, or the statement is `Equiv x x`"
        );
        let concl = equiv(&mut d, p, integral_ab, rhs);

        let ty = {
            let t = d.pi_fv(ucb_fv, ucb_ty, concl);
            let t = d.pi_fv(uac_fv, uac_ty, t);
            let t = d.pi_fv(hcb_fv, hcb_ty, t);
            let t = d.pi_fv(hac_fv, hac_ty, t);
            let t = d.pi_fv(u_fv, u_ty, t);
            let t = d.pi_fv(hab_fv, hab_ty, t);
            let t = d.pi_fv(mcb0_fv, nat, t);
            let t = d.pi_fv(mac0_fv, nat, t);
            let t = d.pi_fv(b_fv, carrier, t);
            let t = d.pi_fv(a_fv, carrier, t);
            d.pi_fv(f_fv, f_ty, t)
        };
        let value = {
            let v = d.lam_fv(ucb_fv, ucb_ty, proof);
            let v = d.lam_fv(uac_fv, uac_ty, v);
            let v = d.lam_fv(hcb_fv, hcb_ty, v);
            let v = d.lam_fv(hac_fv, hac_ty, v);
            let v = d.lam_fv(u_fv, u_ty, v);
            let v = d.lam_fv(hab_fv, hab_ty, v);
            let v = d.lam_fv(mcb0_fv, nat, v);
            let v = d.lam_fv(mac0_fv, nat, v);
            let v = d.lam_fv(b_fv, carrier, v);
            let v = d.lam_fv(a_fv, carrier, v);
            d.lam_fv(f_fv, f_ty, v)
        };

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "integralSplitSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "integral_split_proof must prove additivity at the base split point: {:?}",
            result.err()
        );
    }
}

#[cfg(test)]
mod integral_scale_tests {
    use super::*;
    use crate::Declaration;

    /// **Mandatory concrete instantiation, with a negative (dropped-factor)
    /// control.** `F := fun _ => one`, `c := one + one` (`two`, so scaling is
    /// non-trivial), `a := zero`, `b := one`. The SAME proof term is checked
    /// against BOTH the true conclusion `Equiv (integral combined a b hab
    /// ucF) (mul c (integral F a b hab uF))` (must succeed) and a FALSE
    /// conclusion that drops the `c` factor entirely, `Equiv (integral
    /// combined a b hab ucF) (integral F a b hab uF)` (must be REFUSED) --
    /// genuinely false since `c := two != one`, not merely a vacuous swap.
    #[test]
    fn integral_scale_concrete_and_negative_control() {
        crate::on_a_deep_stack(integral_scale_concrete_and_negative_control_body);
    }

    fn integral_scale_concrete_and_negative_control_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);

        let zero_c = d.kernel().const_(p.zero, vec![]);
        let one_c = d.kernel().const_(p.one, vec![]);
        let two_c = cadd(&mut d, p, one_c, one_c);

        let f_const_one = {
            let ignore_fv = d.fresh_fvar();
            d.lam_fv(ignore_fv, carrier, one_c)
        };

        let a = zero_c;
        let b = one_c;
        let lt01 = d.lemma(p.zero_lt_one, &[]);
        let hab = d.lemma(p.le_of_lt, &[zero_c, one_c, lt01]);

        let uf = d.lemma(p.uniformly_continuous_const, &[one_c, a, b]);

        // combined_val := mul two one -- the value `combined t` reduces to
        // for every `t`, since `f_const_one` ignores its argument.
        let combined_val = cmul(&mut d, p, two_c, one_c);
        let ucf = d.lemma(p.uniformly_continuous_const, &[combined_val, a, b]);

        let proof = d.lemma(p.integral_scale, &[two_c, f_const_one, a, b, hab, uf, ucf]);

        let combined = {
            let ignore_fv = d.fresh_fvar();
            d.lam_fv(ignore_fv, carrier, combined_val)
        };
        let integral_f_val = d.const_app(p.integral, &[f_const_one, a, b, hab, uf]);
        let integral_cf_val = d.const_app(p.integral, &[combined, a, b, hab, ucf]);
        let mul_c_integral_f_val = cmul(&mut d, p, two_c, integral_f_val);

        let anon = d.kernel().anon();

        // Positive: the TRUE conclusion must be accepted.
        let true_ty = equiv(&mut d, p, integral_cf_val, mul_c_integral_f_val);
        let name_ok = d.kernel().name_str(anon, "__integralScaleConcreteOk");
        let result_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: name_ok,
            uparams: vec![],
            ty: true_ty,
            value: proof,
        });
        assert!(
            result_ok.is_ok(),
            "integral_scale at c := two, F := const one, [a,b] := [0,1] must \
             prove `Equiv (integral combined...) (mul c (integral F...))`: {:?}",
            result_ok.err()
        );

        // Negative control: the SAME proof term, asserted against a FALSE
        // conclusion that drops the `c` factor (`two != one`, genuinely
        // false, not a vacuous or inverted control).
        let false_ty = equiv(&mut d, p, integral_cf_val, integral_f_val);
        let name_bad = d.kernel().name_str(anon, "__integralScaleConcreteBad");
        let result_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_bad,
            uparams: vec![],
            ty: false_ty,
            value: proof,
        });
        assert!(
            result_bad.is_err(),
            "the SAME proof term must be REFUSED against the FALSE \
             conclusion that drops the `c` factor: `Equiv (integral \
             combined...) (integral F...)`"
        );
    }
}
