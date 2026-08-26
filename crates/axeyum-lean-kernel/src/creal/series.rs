//! **Finite sums over the constructed reals**, `CReal.sumRange`, and the
//! first genuinely analytic facts about them (monotonicity, the triangle
//! inequality) — the missing floor under every series and every integral over
//! `CReal`.
//!
//! ## The convention, matched to `Nat`/`Complex`
//!
//! `CReal.sumRange` is structural `Nat.rec` on the bound, matching
//! `Nat.sumRange`'s own convention exactly
//! (`nat_prelude/defs.rs::declare_finite_ranges`) and `Complex.sumRange`'s
//! (`complex.rs::declare_sum_range`, landed the same day): `sumRange f zero ≡
//! zero`, `sumRange f (succ j) ≡ add (sumRange f j) (f j)` — recursion on the
//! bound, the new term folded on the **right** of the prior sum. This is the
//! fourth carrier to match this convention (`Int.pow`, `Complex.pow`,
//! `Int.prodRange`, `Complex.sumRange` all did before it); nothing here
//! invents a fifth.
//!
//! `sumRange_zero`/`sumRange_succ` close by `Eq.refl` alone, exactly as
//! `Complex.sumRange_zero`/`_succ` do: `sumRange`'s `Nat.rec` application
//! ι-reduces to the algebraic combinator (`zero`, or `add (sumRange f n) (f
//! n)`) directly, with no `CReal.add`/`CReal.neg` internals ever unfolded to
//! get there, so this is independent of `CReal`'s own carrier being a setoid.
//! Every other law here **does** need `Equiv`, never `Eq`: `CReal.Equiv` is a
//! defined `Prop` relation and nothing rewrites under a `sumRange` for free.
//!
//! ## What the analytic laws needed that did not already exist
//!
//! [`declare_sum_range_add`] needs the four-term rearrangement `(A+B)+(C+D) ~
//! (A+C)+(B+D)` — the `Equiv` promotion of
//! `nat_prelude/binomial.rs::add_add_add_comm` — built inline as
//! [`add4_comm`] rather than declared, exactly as the `Eq Nat` original is
//! only ever a proof-term helper, never a kernel theorem of its own.
//!
//! [`declare_abs_sum_range_le`] (the triangle inequality for a finite sum)
//! needed a two-term triangle inequality `abs_add_le` first, and *that*
//! needed `neg(add a b) ~ add(neg a)(neg b)` — a standard additive-inverse
//! law `CReal` has no standalone declaration for. [`neg_add`] derives it from
//! [`add4_comm`] and the additive-inverse laws (`add_neg`, `add_zero`,
//! `add_comm`, `add_assoc`) by the usual "any right inverse is the inverse"
//! argument, specialised to the one instance needed rather than proved as a
//! general uniqueness lemma. None of `add4_comm`/`neg_add`/`abs_add_le` are
//! declared kernel theorems — they are Rust-level proof-term builders, the
//! same status `add_add_add_comm` has for `Nat`.
//!
//! ## Telescoping, splitting, and the comparison test
//!
//! [`declare_sum_range_telescope`] and [`declare_sum_range_split`] are the
//! two facts every convergence argument over a series opens with — the first
//! collapses `Σ_{k<n} (f(k+1) − f k)` to `f n − f 0`, the second turns a
//! statement about a *tail* of a sum into a statement about a *difference*
//! of two partial sums. Both are induction on `n` closed by algebra alone
//! (no rational estimate): telescoping needs one more cancellation shape,
//! [`cancel_left`] (`(a+b)+(c+(−a)) ~ c+b`, four terms, via [`add4_comm`]),
//! and splitting needs only `Nat.add`'s own iota-reduction plus
//! `add_zero`/`add_assoc`.
//!
//! [`declare_sum_range_tail_le`] is the comparison test itself: `f`
//! pointwise-bounded by `g` in absolute value forces every tail of `f`'s
//! partial sums to be bounded by the corresponding tail of `g`'s. It is
//! **not** stated through `CReal.Cauchy` (`creal/convergence.rs`), and that
//! is a deliberate, considered choice, not an oversight. `CReal.Cauchy`'s
//! body — see that module's own documentation — compares `seq (h m) m`
//! against `seq (h n) n`: the *rational* sample each real offers at **its
//! own canonical index**, the same representative-level machinery
//! `completeness.rs`/`convergence.rs` build extensively for `CReal.add`'s
//! single shift. Reaching that shape for `h := sumRange f` needs a
//! sample-rate law for `sumRange` itself — how `seq (sumRange f n) k`
//! relates to the individual `f i`'s own samples — and every other
//! `sumRange` law in this file, [`declare_sum_range_tail_le`] included, is
//! proved through the abstract `Equiv`/`le`/`abs` algebra alone and never
//! once inspects `seq`. [`declare_sum_range_tail_le`] is the actual
//! mathematical engine of the comparison test — a genuine real-valued tail
//! bound, via [`declare_sum_range_split`] to rewrite each tail as a shifted
//! partial sum ([`cancel_right`]: `(a+b)+(−a) ~ b`), then
//! [`super::CRealPrelude::abs_sum_range_le`] and
//! [`super::CRealPrelude::sum_range_le`] to bound it.
//!
//! ## The sample-rate law itself: cheap in recursive form, not in closed form
//!
//! An earlier slice of this file reported the sample-rate law above as
//! "not existing anywhere in this development" and "plausibly a module the
//! size of `completeness.rs` on its own". The **recursive** form of the law
//! is not that expensive, and [`declare_sum_range_seq_equations`] proves it
//! outright:
//!
//! ```text
//! CReal.sumRange_seq_zero : ∀ f k, Eq Rat (seq (sumRange f Nat.zero) k) Rat.zero
//! CReal.sumRange_seq_succ : ∀ f n k, Eq Rat (seq (sumRange f (Nat.succ n)) k)
//!   (Rat.add (seq (sumRange f n) (shift k)) (seq (f n) (shift k)))
//! ```
//!
//! Both close by `Eq.refl` alone — exactly [`declare_sum_range_equations`]'s
//! own pattern one level deeper. `sumRange f (succ n)` already ι-reduces to
//! `add (sumRange f n) (f n)` ([`declare_sum_range_equations`]'s own
//! content); what makes the `seq`-level law free is that `CReal.add`'s
//! representative is *also* a bare `mk (fun n => …) _` application
//! ([`super::declare_addition`]), so `seq (add x y) k` ι-reduces (through
//! the `CReal.rec`/`CReal.mk` projection [`super::declare_projections`]
//! builds) straight to `seq x (shift k) + seq y (shift k)`, no case split on
//! `x`, `y`, `k`, or `n` required — all of them stay free variables through
//! the whole reduction, which is why the general (`∀ n`) law needs no
//! induction, only ι and β.
//!
//! **This recursion is not the same thing as a *closed form*, and the closed
//! form is where the real cost lives.** Unwinding [`declare_sum_range_seq_equations`]
//! `n` times gives, writing `shift^m` for `shift` iterated `m` times
//! (`shift^0 := id`):
//!
//! ```text
//! seq (sumRange f n) k  =  Σ_{i<n} seq (f i) (shift^{n−i} k)
//! ```
//!
//! i.e. `sumRange f n` sampled at `k` reads term `i` not at `i`'s own
//! canonical index, but at a *deep* index reached by iterating `shift` down
//! from `k`. This is a true statement — provable by induction on `n` from
//! the two equations above — but it is **not declared as a kernel theorem
//! here**, because stating it needs an explicit `Nat → Nat → Nat`
//! shift-iteration combinator (`shift` composed with itself a *symbolic*
//! number of times), which does not exist in this development and is its
//! own small piece of infrastructure (a `Nat.rec` definition plus its own
//! two defining equations, the same shape as [`declare_sum_range`] itself).
//!
//! Nor would the closed form, once stated, be *sufficient* to reach
//! `CReal.Cauchy (sumRange f)` for an arbitrary `f` — and seeing why is the
//! actual load-bearing finding of this slice. `Cauchy`'s bound has to be
//! **uniform in `n`** (one `K`, working for every pair of indices), but
//! bounding `seq (f i) (shift^{n−i} k)` against `f i`'s own canonical sample
//! `seq (f i) i` via [`super::CRealPrelude::regular`] costs
//! `modulus (shift^{n−i} k) i = 1/(shift^{n−i}(k)+1) + 1/(i+1)`. The first
//! term shrinks with more shifting; the **second does not shrink with
//! `n`** — it is `f i`'s own fixed regularity cost, unrelated to how deep
//! `sumRange` samples it. Summing that error over `i < n` costs at least
//! `Σ_{i<n} 1/(i+1)`, the harmonic series, which **diverges** as `n → ∞`. So
//! a per-term bound built this way cannot give a `Cauchy`-shaped estimate
//! uniform in `n`, for any `f` — the closed form is real, but it is the
//! wrong tool for this particular bridge, independent of how carefully it
//! is stated or proved.
//!
//! The tractable route is the one [`declare_sum_range_tail_le`] already
//! reaches partway: convert its **real-valued** tail bound (`CReal.le`,
//! already representative-independent) into a `Cauchy`-shaped raw bound by
//! widening at a *shared* index — the same three-term telescope
//! `completeness.rs::declare_limit_dist` runs (`seq (h m) m − seq (h n) n =
//! (seq (h m) m − seq (h m) j) + (seq (h m) j − seq (h n) j) + (seq (h n) j
//! − seq (h n) n)`, the outer two legs closed by [`super::CRealPrelude::regular`]
//! applied to the *fixed* reals `h m`/`h n` — no deep-shift indices involved
//! — and the middle leg by unfolding [`declare_sum_range_tail_le`]'s
//! `CReal.le` at that same shared index `j`, after deciding which of `m ≤ n`
//! or `n ≤ m` holds so the tail lemma has a `sum_range_split`-shaped
//! difference to work with). That still needs `CReal.abs`'s own `seq`
//! characterisation to unfold the middle leg (untouched by this slice), so
//! it is real remaining work, not a restatement — but it is bounded work of
//! the same shape `limit_dist` already solved, not a fresh harmonic-series
//! dead end.
//!
//! ## The Cauchy-shape conversion: the route closes, but it is a *nested*
//! telescope, not a flat one — read this before attempting it
//!
//! A later slice worked the construction above through to concrete term
//! level (never committed — see below for why) and the previous framing
//! understated its size by roughly 3–5×. The one paragraph above still
//! describes the *outer* structure correctly, but "the middle leg by
//! unfolding `sum_range_tail_le`'s `CReal.le`" is doing a lot of hidden
//! work: unfolding that `CReal.le` at the shared index gives a bound on
//! `seq (h m) j − seq (h n) j` **in terms of `seq (tail_g) j`**, i.e. in
//! terms of `g`'s own comparison-sequence sample at `j` — and `tail_g` is
//! itself `sumRange g (m+n) − sumRange g m`, an `add`/`neg` term whose
//! `seq` at `j` shifts (`seq (add x y) k` samples `x`, `y` at `shift k`,
//! never at `k`). Turning *that* into something usable needs a **second,
//! independent instance of the same three-leg telescope**, applied to `g`'s
//! own partial sums and anchored at `g`'s own Cauchy witness. Concretely,
//! for `CReal.sumRange_cauchy_of_dominated : ∀ f g, (∀ k, le (abs (f k)) (g
//! k)) → Cauchy (sumRange g) → Cauchy (sumRange f)` (the natural statement
//! of this piece — it has to conclude the *existential* `Cauchy`, not a bare
//! `Within`, because the bound it produces genuinely mentions `g`'s Cauchy
//! witness `K`, and only wrapping the conclusion in its own `∃ K'` lets that
//! dependency out of an `Exists.rec` motive):
//!
//! - **Outer telescope**, at shared index `t := shift q` (`q := m+n`, the
//!   ordering `sum_range_tail_le` already bakes in via its own `m`, `add m
//!   n` parameters — no `Nat.le_total` case split needed for *this* half):
//!   `seq (sumRange f m) m − seq (sumRange f q) q` splits into a leg from
//!   `CReal.regular (sumRange f m) m t`, a middle leg, and a leg from
//!   `CReal.regular (sumRange f q) t q`. The middle leg is (up to sign)
//!   `seq tail_f j` at `j := q`, bounded via `le_trans le_abs_self
//!   sum_range_tail_le` / `le_trans neg_le_abs sum_range_tail_le` (**two**
//!   one-sided real bounds, not one `abs_le` call, because `abs_le`'s
//!   hypothesis shape does not survive sampling at an index) applied at
//!   `q`, against `seq tail_g q`.
//! - **Inner telescope**, same shared-index shape but anchored through `m`
//!   and `q` themselves (not through `t` a second time): `seq tail_g q`
//!   unfolds (`add`'s own shift) to `seq (sumRange g q) t − seq (sumRange g
//!   m) t`, and *that* is bounded by routing through `seq (sumRange g m) m
//!   − seq (sumRange g q) q` — exactly `Cauchy (sumRange g)`'s witness
//!   applied at `(m, q)`, no index gymnastics needed for that piece — plus
//!   the same two `CReal.regular`-at-`(_, t)` legs used in the outer
//!   telescope (reused, not re-derived).
//!
//! **The sign/associativity bookkeeping is the actual cost, not the
//! mathematics.** Every `seq (add x y) k` unfold only gets you as far as
//! `Rat.sub`/`Rat.neg` applied in whatever nesting the source term had —
//! e.g. `seq (neg tail_f) q` reduces (pure ι/β, free) to `Rat.neg (Rat.sub
//! (seq A_q t) (seq A_m t))`, and turning that into the `Rat.sub (seq A_m
//! t) (seq A_q t)` shape the telescope's other legs use needs an *explicit*
//! `Rat.neg_sub` rewrite — defeq does computation, not ring identities, and
//! this construction needs the identity at nearly every join. `Rat.le_of_sub_le`
//! (`u ≤ v+q → ⊢ u−v ≤ q`, already declared) plus `Rat.neg_sub` supply the
//! sign flips; `Rat.sub_add_sub` supplies each telescoping join; `Rat.bounds_add`/
//! `Rat.bounds_neg` combine two-sided bounds; `half_shift_le`
//! (`completeness.rs`, already `pub(super)`) widens every `1/(shift q+1)`
//! leg up to `1/(q+1)` so `t` never survives into the final bound;
//! `Rat.nat_div_succ_add` fuses same-index terms and `Rat.nat_div_succ_le_add_left`
//! pads whichever of the two final coefficients is smaller so both sides
//! share one witness `K`, as `Cauchy`'s shape requires.
//!
//! Worked all the way through by hand, this is on the order of **35–45
//! distinct proof-term steps** (roughly matching `declare_converges_cauchy`
//! and `regroup_middle_four` combined, which solve a structurally similar
//! but *single*, not *nested*, three-term telescope) — **not committed this
//! slice**, because a construction this size, assembled in one pass without
//! kernel-checking each join, is exactly the failure mode this repository's
//! own history warns about (`EIGHT argument-position defects` in one day,
//! five in the `symm` family) and a kernel declaration has no "mostly
//! right" state: it either checks or it does not exist. The next attempt
//! should land the inner and outer telescopes as **separately kernel-tested
//! pieces** (e.g. first the `within`-swap-via-`neg_sub` helper and the
//! inner telescope alone, verified against a trivial `f = g` instance,
//! *then* the outer one) rather than as one unverified block.
//!
//! **The `within`-swap helper and the inner telescope are now both landed**
//! — [`within_of_tail_le`] (used inside [`declare_sum_range_tail_within`])
//! and [`declare_sum_range_tail_cauchy_within`], each kernel-checked and
//! verified against a trivial `g = (fun _ => zero)` instance
//! (`creal_tests.rs`). The inner telescope turned out to need no `Rat.neg`
//! anywhere — the three legs (`CReal.regular` at `(sumRange g q, t, q)`, the
//! raw Cauchy witness applied at `(q, m)`, `CReal.regular` at `(sumRange g
//! m, m, t)`) already share consecutive endpoints in the right order, so two
//! direct `Rat.sub_add_sub` rewrites suffice ([`chain_within3`]) rather than
//! `declare_converges_cauchy`'s `regroup_middle_four` regrouping — closer to
//! `declare_limit_dist`'s own two-leg shape, one leg longer, than to the
//! single-telescope estimate above.
//!
//! **The outer telescope is now landed too**
//! ([`declare_sum_range_tail_within_cauchy`]), and it turned out to be
//! bound-widening glue, not a further telescope: both legs it needed
//! ([`declare_sum_range_tail_within`]'s `Within u (v+w)` and
//! [`declare_sum_range_tail_cauchy_within`]'s `Within v B`, the same `v`
//! built identically by both from the same `m`, `n`) were already landed, so
//! combining them is one [`weaken`] call against `le (v+w) (B+w)` — itself
//! one `Rat.add_le_add` on `B`'s upper half paired with `Rat.le_refl w`. The
//! earlier "at least three comparably sized pieces" estimate for this step
//! specifically (as opposed to the two gaps below, which are real and
//! unaffected) overstated it in the same direction the module's two earlier
//! retrospectives already flagged: once the pieces it composes existed, the
//! composition itself did not need its own telescope.
//!
//! What this theorem does **not** yet supply is the `Nat.le_total`
//! orientation selection over an *arbitrary* pair `(m, n)` (as opposed to
//! the ordered pair `(m, add m n)` both `declare_sum_range_tail_within` and
//! this theorem work with directly) — [`declare_sum_range_tail_within_le`]
//! already has that content, but wiring it through this theorem's own
//! `Within` bound to reach `CReal.Cauchy`'s `∀ m n` shape is left to
//! whichever future piece assembles `sumRange_cauchy_of_dominated` itself,
//! along with the two further gaps below.
//!
//! **That "wiring through" undercounted its own size by one more hidden
//! step, and the step is now landed.** `declare_sum_range_tail_within_cauchy`'s
//! conclusion is a bound on `seq (add (sumRange f (add m n)) (neg (sumRange
//! f m))) (add m n)`, and unfolding `CReal.add`'s `seq` equation (the same
//! ι/β argument [`declare_sum_range_seq_equations`]'s doc comment gives)
//! shows this samples **both** `sumRange f (add m n)` and `sumRange f m` at
//! the *shifted* index `t := shift (add m n)`, never at their own canonical
//! indices `add m n` and `m`. `CReal.Cauchy`'s own body is stated at exactly
//! those canonical indices (`seq (f p) p − seq (f qq) qq`), so
//! `sum_range_tail_within_cauchy`'s conclusion — even lifted to an arbitrary
//! pair by `sum_range_tail_within_le`'s own technique — is **not yet** in
//! `Cauchy`-callable shape. Reaching it needs two more `CReal.regular` legs
//! per side (`seq (sumRange f q) q` against `seq (sumRange f q) t`, and
//! `seq (sumRange f m) m` against `seq (sumRange f m) t`), chained through
//! the already-landed bound via [`chain_within3`] a *second* time — not the
//! `X → Y → Z → W` order `sum_range_tail_cauchy_within`'s own inner
//! telescope uses (there the middle leg was the *known* raw Cauchy witness
//! for `g`; here the middle leg is the *known* quantity —
//! `sum_range_tail_within_cauchy`'s own conclusion — and the canonical
//! difference is what's wanted, so the known bound sits in the middle of
//! the chain, `Y → X → W → Z`, rather than at an end). [`within_symm`]
//! (`Within (a−b) q → Within (b−a) q`, via `Rat.neg_sub` + `Rat.bounds_neg`)
//! supplies the two regularity legs' needed orientation.
//!
//! **[`dominated_canonical_at`] does exactly this, and
//! [`declare_sum_range_cauchy_dominated_ordered`] lifts it to an arbitrary
//! `a ≤ b` via `Nat.le_dest` + transport — `sum_range_tail_within_le`'s own
//! technique, reused against this different, canonical-shape payload rather
//! than re-derived.** Both are landed and kernel-checked (verified at the
//! non-degenerate `a = 0, b = 1` instance, `creal_tests.rs`).
//!
//! **All three gaps this section used to list are now landed —
//! [`declare_sum_range_cauchy_of_dominated`] closes
//! `CReal.sumRange_cauchy_of_dominated`, kernel-checked (`creal_tests.rs`,
//! `f = g` the constant-zero sequence, a genuine `K = 0` `Exists.intro`
//! witness — the theorem's own generic type-check already exercises both
//! `Nat.le_total` branches, since a Pi body is checked once against a fresh
//! free variable, not once per instantiation).** The previous brief's
//! per-branch prediction had the right total repair (one [`within_symm`]
//! flip, one `Rat.add_comm`) but the wrong branch: calling
//! `sum_range_cauchy_dominated_ordered_normalized` at `(a, b) := (n, m)`
//! whenever `Nat.le n m` holds lands **exactly** on `Cauchy`'s own `(m, n)`
//! sample and `radd` order, no rewrite at all — this theorem's bound
//! genuinely is not symmetric in `a`/`b` (the `t`-side legs always attach to
//! the larger argument `b`), so which pairing is "free" is fixed by that
//! asymmetry, not a 50/50 choice. The `Nat.le m n` branch (`(a, b) := (m,
//! n)`) carries both repairs together: `within_symm` flips the raw `seq (f
//! n) n − seq (f m) m)` to `Cauchy`'s wanted `seq (f m) m − seq (f n) n)`,
//! and `Rat.add_comm` reorders the still-`(n, m)`-ordered bound
//! `within_symm` leaves untouched to `Cauchy`'s `(m, n)` order. Both
//! branches close over the **same** `K' := k + 8`, built once outside the
//! split as eight bare `Nat.succ`s of the raw Cauchy witness `k` (not the
//! source theorem's own nested-`Nat.add`-by-literal chain — both reduce to
//! the identical `succ` tower, but a bare `succ` chain has no `Nat.add`
//! operand-order trap to fall into at all).
//!
//! - **Bound normalization** (also landed, by an earlier slice):
//!   [`declare_sum_range_cauchy_dominated_ordered_normalized`] widens
//!   `sum_range_cauchy_dominated_ordered`'s eleven-`Rat.natDivSucc`-leaf
//!   bound (four copies of `1/(shift b+1)`, widened to `1/(b+1)` via
//!   `half_shift_le`) down to the single-`K'` `natDivSucc K' b + natDivSucc
//!   K' a` shape `CReal.Cauchy` needs, via `Rat.natDivSucc_add` fusion and
//!   one `Rat.natDivSucc_le_add_left` pad — the same three lemmas
//!   `declare_converges_cauchy`'s `regroup_middle_four` uses one telescope
//!   down. [`declare_sum_range_cauchy_of_dominated`] reuses this theorem
//!   directly rather than re-deriving the normalization.
//! - **The `CReal.Cauchy` existential itself** (landed by this slice):
//!   [`declare_sum_range_cauchy_of_dominated`] eliminates the hypothesis
//!   (`int_prelude::ops::exists_elim`, elem type `Nat` — the same idiom
//!   [`declare_sum_range_cauchy_dominated_ordered`] already uses against a
//!   *different* `Nat`-witnessed existential, `Nat.le_dest`'s) and
//!   introduces the conclusion (`Exists.intro` at `K' := k + 8`) around the
//!   `Nat.le_total` case split above — confirming
//!   `declare_converges_cauchy`'s (`creal/convergence.rs`) prediction that
//!   this shape is tractable, not merely assuming it so.
//!
//! ## Two further gaps this slice found, neither in the previous brief
//!
//! Even a landed `sumRange_cauchy_of_dominated` does **not** reach `Σ b`
//! converges by itself, for a reason independent of the telescope above:
//!
//! 1. **~~There is no bridge from a `K`-scaled `Cauchy` witness to an actual
//!    limit.~~ STALE as of `convergence.rs`/`speedup.rs` (checked
//!    2026-08-26): that bridge is landed, just not through
//!    `completeness.rs`.** `completeness.rs` builds `CReal.limit`/
//!    `CReal.limit_dist` only for `CReal.RegularSeq` — the **unscaled**,
//!    `K = 1` case (`modulus m n = 1/(m+1)+1/(n+1)` literally, not `≤`) — and
//!    routing a `K`-scaled `Cauchy f` through THAT route needs exactly the
//!    reindexing this item used to describe as absent. But
//!    [`CRealPrelude::regular_of_scaled_cauchy`] and
//!    [`CRealPrelude::converges_of_cauchy`] (`creal/convergence.rs`, plus
//!    [`CRealPrelude::speedup`] in `creal/speedup.rs`) are a DIFFERENT,
//!    already-landed route to the same destination: they resample the
//!    **diagonal** `fun n => seq (f n) n` directly via `speedup` rather than
//!    going through `RegularSeq`/`limit` at all, and both are declared in
//!    `build_creal_prelude`'s dispatch order BEFORE this module's own
//!    [`declare_series`] runs — so this environment already had them when
//!    the paragraph below was written. `CRealPrelude::converges_of_cauchy`'s
//!    own doc comment names exactly why `RegularSeq`/`limit` is the wrong
//!    tool here: that route "forces a [`CRealPrelude::regular`] bridge at
//!    the *shallow* outer index on top of the Cauchy estimate, which costs a
//!    whole extra `1/(m+1)` per side and overshoots `RegularSeq`'s fixed
//!    modulus by a factor of two", while `speedup`'s own sample *is* the
//!    diagonal value and needs no such bridge. So: **not** a gap in this
//!    development, only in `completeness.rs`'s own more limited route
//!    through it — do not build a second, parametrised completeness
//!    construction to close this; call `converges_of_cauchy` instead. This
//!    still blocks **both** `converges_geometric` (item 2) and the
//!    comparison test's conclusion (item 3, which needs an actual
//!    `Converges (sumRange a) L`, not just `Cauchy (sumRange a)`) — the
//!    comparison test does not avoid this by taking `Converges (sumRange
//!    b) M` as a hypothesis, because it still has to *produce* a limit for
//!    `sumRange a` — but the remaining work is wiring `converges_of_cauchy`
//!    onto `sumRange_cauchy_of_dominated`'s conclusion, not writing a new
//!    completeness construction from scratch.
//! 2. **`converges_geometric` needs a quantitative decay rate that also
//!    does not exist.** [`CRealPrelude::geom_tail_bounded`] bounds `(1 − x)
//!    · |tail| ≤ xᵐ`, not `|tail| ≤ xᵐ/(1 − x)` — going from the first to
//!    the second needs a "cancel a positive, apart-from-zero real factor
//!    from a `CReal.le`" lemma, and there is no such lemma over `CReal` in
//!    this codebase (checked: no `le_of_mul_le`/`div_le`/`le_div`/
//!    `mul_le_cancel` declared). And even granting that division, `Cauchy`'s
//!    shape needs `xᵐ ≤ C/(m+1)` for a *fixed* `C` — true for a witnessed
//!    ratio (`x ≤ N/(N+1)`) but itself a genuine calculus fact (Bernoulli's
//!    inequality or equivalent), not a restatement of anything already
//!    proved here.
//!
//! Net: the previous lane's "bounded work of the same shape `limit_dist`
//! already solved" undercounted by treating the tail-bound conversion as
//! the only remaining step. It was the first of what this doc used to size
//! as three comparably sized pieces; checked 2026-08-26, the second (the
//! `Cauchy`→`Converges` reindexing bridge) is **already landed** as
//! `CRealPrelude::converges_of_cauchy`/`regular_of_scaled_cauchy` — see item
//! 1 above — so what remains is the nested telescope above (landed this
//! slice), wiring `converges_of_cauchy` onto `sumRange_cauchy_of_dominated`'s
//! conclusion (small — a direct application, no new construction), and the
//! geometric decay-rate quantification (item 2, still a genuine gap). None
//! of the three should be attempted as a single unverified slice.

use super::completeness::half_shift_le;
use super::convergence::{converges_applied, exists_elim as creal_exists_elim, exists_ty};
use super::ring_helpers::add4_comm;
use super::{
    CRealPrelude, DERIVED_HEIGHT, and_intro, creal_ty, div_succ, equiv, halves, modulus, sample,
    shift, weaken, within,
};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{
    nat_rewrite_prop, radd, rat_eq_rewrite, rchain, rcongr, req, rle, rneg, rrefl, rsymm, rzero,
};

/// Admit `CReal.sumRange`, its defining equations, congruence, additivity,
/// scalar distribution, monotonicity, and the triangle inequality.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_series(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_sum_range(d, p)?;
    declare_sum_range_equations(d, p)?;
    declare_sum_range_congr(d, p)?;
    declare_sum_range_add(d, p)?;
    declare_mul_sum_range(d, p)?;
    declare_sum_range_le(d, p)?;
    declare_mono_of_le_succ(d, p)?;
    declare_sum_range_mono_outer(d, p)?;
    declare_abs_sum_range_le(d, p)?;
    declare_sum_range_telescope(d, p)?;
    declare_sum_range_split(d, p)?;
    declare_sum_range_tail_le(d, p)?;
    declare_sum_range_tail_within(d, p)?;
    declare_sum_range_tail_within_le(d, p)?;
    declare_sum_range_tail_cauchy_within(d, p)?;
    declare_sum_range_tail_within_cauchy(d, p)?;
    declare_sum_range_cauchy_dominated_ordered(d, p)?;
    declare_sum_range_cauchy_dominated_ordered_normalized(d, p)?;
    declare_sum_range_cauchy_of_dominated(d, p)?;
    declare_sum_range_converges_of_dominated(d, p)?;
    declare_sum_range_comparison_test(d, p)?;
    declare_sum_range_seq_equations(d, p)
}

// --- small local term builders ----------------------------------------------

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

fn cle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.le, &[x, y])
}

/// `λ k, f (add m k)` — `f` shifted by `m`, the summand
/// [`declare_sum_range_split`] and [`declare_sum_range_tail_le`] both build,
/// as one shared function so the two never drift into structurally distinct
/// (merely defeq) closures.
fn shifted_fn(d: &mut IntDev<'_>, m: ExprId, f: ExprId) -> ExprId {
    let nat_add = d.prelude().add;
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let mk = d.const_app(nat_add, &[m, k]);
    let body = d.apply(f, &[mk]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Eq.{1} CReal a b`.
fn creal_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let eq = d.kernel().const_(logic.eq, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(eq, &[carrier, a, b])
}

/// `Eq.refl.{1} CReal a`.
fn creal_eq_refl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let refl = d.kernel().const_(logic.eq_refl, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(refl, &[carrier, a])
}

/// Chain `Equiv start …` through `(next, step)` pairs, the way
/// `super::product::equiv_chain`/`super::inverse::echain` do — rebuilt here
/// (both of those are private to their own modules) rather than imported.
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

/// `(a+b)+(c+d) ~ (a+c)+(b+d)`, returned as a `(target, proof)` chain step
/// (the proof's source is `add(add(a,b),add(c,d))`) — the `Equiv` promotion
/// of `nat_prelude/binomial.rs::add_add_add_comm`.
/// `Equiv (neg zero) zero`, as a proof term — the group identity `−0 = 0`,
/// from [`CRealPrelude::add_zero`]/[`CRealPrelude::add_comm`]/
/// [`CRealPrelude::add_neg`] rather than any `Rat`-level fact (`CReal` has no
/// standalone `neg_zero` law).
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]); // add nz zero ~ nz
    let step1 = d.lemma(p.equiv_symm, &[padded, nz, h1]); // nz ~ padded
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]); // padded ~ flipped
    let h3 = d.lemma(p.add_neg, &[zero_c]); // flipped ~ zero
    echain(d, p, nz, &[(padded, step1), (flipped, h2), (zero_c, h3)])
}

/// `Equiv (neg (add a b)) (add (neg a) (neg b))` — additive inverse
/// distributes over `add`. Proved inline via [`add4_comm`] and the
/// additive-inverse laws by the usual "any right inverse of `a+b` is `−(a+b)`"
/// argument, specialised to the witness `(−a)+(−b)` rather than proved as a
/// general uniqueness lemma.
fn neg_add(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let s = cadd(d, p, a, b);
    let na = cneg(d, p, a);
    let nb = cneg(d, p, b);
    let t = cadd(d, p, na, nb);
    let ns = cneg(d, p, s);

    // f_proof : Equiv (add s t) zero, via add4_comm + the two `add_neg`s.
    let f_proof = {
        let (target1, h4) = add4_comm(d, p, a, b, na, nb);
        // target1 = add (add a na) (add b nb)
        let a_na = cadd(d, p, a, na);
        let b_nb = cadd(d, p, b, nb);
        let add_zz = cadd(d, p, zero_c, zero_c);
        let h_a = d.lemma(p.add_neg, &[a]); // a_na ~ zero
        let h_b = d.lemma(p.add_neg, &[b]); // b_nb ~ zero
        let h5 = d.lemma(p.add_congr, &[a_na, zero_c, b_nb, zero_c, h_a, h_b]); // target1 ~ add_zz
        let h6 = d.lemma(p.add_zero, &[zero_c]); // add_zz ~ zero
        let start = cadd(d, p, s, t);
        echain(d, p, start, &[(target1, h4), (add_zz, h5), (zero_c, h6)])
    };

    // neg s ~ add(neg s)(zero) ~ add(neg s)(add s t) ~ (add(neg s)s)+t ~ add zero t ~ t
    let step_a_target = cadd(d, p, ns, zero_c);
    let step_a = {
        let h = d.lemma(p.add_zero, &[ns]); // step_a_target ~ ns
        d.lemma(p.equiv_symm, &[step_a_target, ns, h]) // ns ~ step_a_target
    };

    let st = cadd(d, p, s, t);
    let step_b_target = cadd(d, p, ns, st);
    let step_b = {
        let f_symm = d.lemma(p.equiv_symm, &[st, zero_c, f_proof]); // zero ~ add s t
        let refl_ns = d.lemma(p.equiv_refl, &[ns]);
        d.lemma(p.add_congr, &[ns, ns, zero_c, st, refl_ns, f_symm])
        // step_a_target ~ step_b_target
    };

    let ns_s = cadd(d, p, ns, s);
    let step_c_target = cadd(d, p, ns_s, t);
    let step_c = {
        let assoc = d.lemma(p.add_assoc, &[ns, s, t]); // step_c_target ~ step_b_target
        d.lemma(p.equiv_symm, &[step_c_target, step_b_target, assoc])
        // step_b_target ~ step_c_target
    };

    let step_d_target = cadd(d, p, zero_c, t);
    let step_d = {
        let x = {
            let comm = d.lemma(p.add_comm, &[ns, s]); // ns_s ~ add s ns
            let s_ns = cadd(d, p, s, ns);
            let negl = d.lemma(p.add_neg, &[s]); // add s ns ~ zero
            d.lemma(p.equiv_trans, &[ns_s, s_ns, zero_c, comm, negl])
        };
        // x : ns_s ~ zero
        let refl_t = d.lemma(p.equiv_refl, &[t]);
        d.lemma(p.add_congr, &[ns_s, zero_c, t, t, x, refl_t])
        // step_c_target ~ step_d_target
    };

    let t_zero = cadd(d, p, t, zero_c);
    let step_e = {
        let comm = d.lemma(p.add_comm, &[zero_c, t]); // step_d_target ~ t_zero
        let collapse = d.lemma(p.add_zero, &[t]); // t_zero ~ t
        d.lemma(p.equiv_trans, &[step_d_target, t_zero, t, comm, collapse])
        // step_d_target ~ t
    };

    echain(
        d,
        p,
        ns,
        &[
            (step_a_target, step_a),
            (step_b_target, step_b),
            (step_c_target, step_c),
            (step_d_target, step_d),
            (t, step_e),
        ],
    )
}

/// `Equiv (add (add a b) (neg a)) b` — the group cancellation `(a+b)+(−a) ~
/// b`, via `add_comm`, `add_assoc`, `add_neg`, `add_zero`.
fn cancel_right(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let ab = cadd(d, p, a, b);
    let start = cadd(d, p, ab, na);

    // (a+b)+(-a) ~ (b+a)+(-a)
    let ba = cadd(d, p, b, a);
    let comm1 = d.lemma(p.add_comm, &[a, b]); // ab ~ ba
    let refl_na = d.lemma(p.equiv_refl, &[na]);
    let s1 = cadd(d, p, ba, na);
    let h1 = d.lemma(p.add_congr, &[ab, ba, na, na, comm1, refl_na]);

    // (b+a)+(-a) ~ b+(a+(-a))
    let a_na = cadd(d, p, a, na);
    let s2 = cadd(d, p, b, a_na);
    let h2 = d.lemma(p.add_assoc, &[b, a, na]); // s1 ~ s2

    // b+(a+(-a)) ~ b+zero
    let zero_c = czero(d, p);
    let h_an = d.lemma(p.add_neg, &[a]); // a_na ~ zero
    let refl_b = d.lemma(p.equiv_refl, &[b]);
    let s3 = cadd(d, p, b, zero_c);
    let h3 = d.lemma(p.add_congr, &[b, b, a_na, zero_c, refl_b, h_an]); // s2 ~ s3

    // b+zero ~ b
    let h4 = d.lemma(p.add_zero, &[b]); // s3 ~ b

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (b, h4)])
}

/// `(target, proof)` with `target = add c b` and `proof : Equiv (add (add a
/// b) (add c (neg a))) target` — cancel `a` against its negation across a
/// four-term sum. Reorders the second pair via `add_comm` so
/// [`add4_comm`] lines `a` up against `neg a`, then one more `add_neg` /
/// `add_zero` / `add_comm` collapses the rest, mirroring [`neg_add`]'s own
/// "witness-specialised inverse" recipe.
fn cancel_left(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> (ExprId, ExprId) {
    let na = cneg(d, p, a);
    let ab = cadd(d, p, a, b);
    let c_na = cadd(d, p, c, na);
    let start = cadd(d, p, ab, c_na);

    // c+(-a) ~ (-a)+c
    let na_c = cadd(d, p, na, c);
    let comm1 = d.lemma(p.add_comm, &[c, na]); // c_na ~ na_c
    let refl_ab = d.lemma(p.equiv_refl, &[ab]);
    let s1 = cadd(d, p, ab, na_c);
    let h1 = d.lemma(p.add_congr, &[ab, ab, c_na, na_c, refl_ab, comm1]);

    // (a+b)+(na+c) ~ (a+na)+(b+c), via add4_comm(a,b,na,c)
    let (s2, h2) = add4_comm(d, p, a, b, na, c);

    // a+na ~ zero
    let a_na = cadd(d, p, a, na);
    let bc = cadd(d, p, b, c);
    let zero_c = czero(d, p);
    let h_an = d.lemma(p.add_neg, &[a]); // a_na ~ zero
    let refl_bc = d.lemma(p.equiv_refl, &[bc]);
    let s3 = cadd(d, p, zero_c, bc);
    let h3 = d.lemma(p.add_congr, &[a_na, zero_c, bc, bc, h_an, refl_bc]); // s2 ~ s3

    // zero+bc ~ bc+zero
    let bc_zero = cadd(d, p, bc, zero_c);
    let h4 = d.lemma(p.add_comm, &[zero_c, bc]); // s3 ~ bc_zero

    // bc+zero ~ bc
    let h5 = d.lemma(p.add_zero, &[bc]); // bc_zero ~ bc

    // bc ~ cb
    let cb = cadd(d, p, c, b);
    let h6 = d.lemma(p.add_comm, &[b, c]); // bc ~ cb
    let target = cb;

    let proof = echain(
        d,
        p,
        start,
        &[
            (s1, h1),
            (s2, h2),
            (s3, h3),
            (bc_zero, h4),
            (bc, h5),
            (target, h6),
        ],
    );
    (target, proof)
}

/// `le (abs (add a b)) (add (abs a) (abs b))` — the two-term triangle
/// inequality, from [`CRealPrelude::abs_le`] with
/// [`CRealPrelude::add_le_add`]/[`CRealPrelude::le_abs_self`] for the lower
/// branch and [`neg_add`] plus [`CRealPrelude::neg_le_abs`] for the upper
/// (negated) branch.
fn abs_add_le(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let s = cadd(d, p, a, b);
    let abs_a = cabs(d, p, a);
    let abs_b = cabs(d, p, b);
    let bound = cadd(d, p, abs_a, abs_b);

    // premise1 : le (add a b) (add (abs a) (abs b))
    let le_a = d.lemma(p.le_abs_self, &[a]);
    let le_b = d.lemma(p.le_abs_self, &[b]);
    let premise1 = d.lemma(p.add_le_add, &[a, abs_a, b, abs_b, le_a, le_b]);

    // premise2 : le (neg (add a b)) (add (abs a) (abs b))
    let na = cneg(d, p, a);
    let nb = cneg(d, p, b);
    let t = cadd(d, p, na, nb);
    let ns = cneg(d, p, s);
    let na_eq = neg_add(d, p, a, b); // ns ~ t
    let step1 = d.lemma(p.le_of_equiv, &[ns, t, na_eq]); // le ns t
    let nle_a = d.lemma(p.neg_le_abs, &[a]); // le na abs_a
    let nle_b = d.lemma(p.neg_le_abs, &[b]); // le nb abs_b
    let step2 = d.lemma(p.add_le_add, &[na, abs_a, nb, abs_b, nle_a, nle_b]); // le t bound
    let premise2 = d.lemma(p.le_trans, &[ns, t, bound, step1, step2]);

    d.lemma(p.abs_le, &[s, bound, premise1, premise2])
}

// --- the declarations --------------------------------------------------------

/// `CReal.sumRange : (Nat → CReal) → Nat → CReal`, structural `Nat.rec` on
/// the bound. See the module documentation for the convention.
fn declare_sum_range(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = d.kernel().const_(p.zero, vec![]);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let body = d.const_app(p.add, &[ih, fj]);
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
        name: p.sum_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 41),
    })
}

/// `CReal.sumRange_zero`/`CReal.sumRange_succ`: the defining equations of
/// [`declare_sum_range`], each closed by `Eq.refl` alone since `sumRange`'s
/// `Nat.rec` application ι-reduces on both minor premises.
fn declare_sum_range_equations(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    // sumRange_zero : ∀ f, Eq CReal (sumRange f Nat.zero) zero.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero_n = d.zero();
        let lhs = d.const_app(p.sum_range, &[f, zero_n]);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        let stmt = creal_eq(d, p, lhs, zero_c);
        let proof = creal_eq_refl(d, p, zero_c);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_range_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // sumRange_succ : ∀ f (n : Nat),
    //   Eq CReal (sumRange f (succ n)) (add (sumRange f n) (f n)).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = d.const_app(p.sum_range, &[f, sn]);
        let prior = d.const_app(p.sum_range, &[f, n]);
        let fj = d.apply(f, &[n]);
        let rhs = d.const_app(p.add, &[prior, fj]);
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
            name: p.sum_range_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `CReal.sumRange_congr : ∀ f g n, (∀ i, Equiv (f i) (g i)) → Equiv
/// (sumRange f n) (sumRange g n)`. Induction on `n`, mirroring
/// `Complex.sumRange_congr`'s own proof shape.
fn declare_sum_range_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let eqv = equiv(d, p, fi, gi);
        d.pi_fv(i_fv, nat, eqv)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.const_app(p.sum_range, &[g, x]);
        equiv(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_c = d.kernel().const_(p.zero, vec![]);
            d.lemma(p.equiv_refl, &[zero_c])
        },
        &|d, j, ih| {
            let f_prior = d.const_app(p.sum_range, &[f, j]);
            let g_prior = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);

            let start = d.const_app(p.add, &[f_prior, fj]);
            let mid = d.const_app(p.add, &[g_prior, fj]);
            let refl_fj = d.lemma(p.equiv_refl, &[fj]);
            let h1 = d.lemma(p.add_congr, &[f_prior, g_prior, fj, fj, ih, refl_fj]);

            let end = d.const_app(p.add, &[g_prior, gj]);
            let pointwise_j = d.apply(h, &[j]);
            let refl_g_prior = d.lemma(p.equiv_refl, &[g_prior]);
            let h2 = d.lemma(
                p.add_congr,
                &[g_prior, g_prior, fj, gj, refl_g_prior, pointwise_j],
            );

            d.lemma(p.equiv_trans, &[start, mid, end, h1, h2])
        },
        n,
    );

    let ty = {
        let with_h = d.pi_fv(h_fv, pointwise, stmt);
        let over_n = d.pi_fv(n_fv, nat, with_h);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, pointwise, proof);
        let over_n = d.lam_fv(n_fv, nat, with_h);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_add : ∀ f g n, Equiv (sumRange (fun i => add (f i) (g i))
/// n) (add (sumRange f n) (sumRange g n))`. Induction on `n`; the successor
/// case needs [`add4_comm`].
fn declare_sum_range_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let combined_fn = |d: &mut IntDev<'_>, f: ExprId, g: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let body = d.const_app(p.add, &[fi, gi]);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let combined = combined_fn(d, f, g);
        let lhs = d.const_app(p.sum_range, &[combined, x]);
        let sf = d.const_app(p.sum_range, &[f, x]);
        let sg = d.const_app(p.sum_range, &[g, x]);
        let rhs = cadd(d, p, sf, sg);
        equiv(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_c = czero(d, p);
            let add_zz = cadd(d, p, zero_c, zero_c);
            let h = d.lemma(p.add_zero, &[zero_c]); // add zero zero ~ zero
            d.lemma(p.equiv_symm, &[add_zz, zero_c, h]) // zero ~ add zero zero
        },
        &|d, j, ih| {
            let combined = combined_fn(d, f, g);
            let scj = d.const_app(p.sum_range, &[combined, j]);
            let sf_j = d.const_app(p.sum_range, &[f, j]);
            let sg_j = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let fgj = cadd(d, p, fj, gj);

            let start = cadd(d, p, scj, fgj);
            let sfsg = cadd(d, p, sf_j, sg_j);
            let s1 = cadd(d, p, sfsg, fgj);
            let refl_fgj = d.lemma(p.equiv_refl, &[fgj]);
            let h1 = d.lemma(p.add_congr, &[scj, sfsg, fgj, fgj, ih, refl_fgj]);

            let (target, h2) = add4_comm(d, p, sf_j, sg_j, fj, gj);

            echain(d, p, start, &[(s1, h1), (target, h2)])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.mul_sumRange : ∀ w f n, Equiv (mul w (sumRange f n)) (sumRange
/// (fun i => mul w (f i)) n)` — a constant distributes through a finite sum,
/// mirroring `Complex.mul_sumRange`'s own proof shape.
fn declare_mul_sum_range(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let scaled_fn = |d: &mut IntDev<'_>| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = d.const_app(p.mul, &[w, fi]);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs_sum = d.const_app(p.sum_range, &[f, x]);
        let lhs = d.const_app(p.mul, &[w, lhs_sum]);
        let scaled = scaled_fn(d);
        let rhs = d.const_app(p.sum_range, &[scaled, x]);
        equiv(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| d.lemma(p.mul_zero, &[w]),
        &|d, j, ih| {
            let prior = d.const_app(p.sum_range, &[f, j]);
            let fj = d.apply(f, &[j]);
            let extended = cadd(d, p, prior, fj);
            let start = d.const_app(p.mul, &[w, extended]);

            let w_prior = d.const_app(p.mul, &[w, prior]);
            let w_fj = d.const_app(p.mul, &[w, fj]);
            let distributed = cadd(d, p, w_prior, w_fj);
            let h1 = d.lemma(p.left_distrib, &[w, prior, fj]);

            let scaled = scaled_fn(d);
            let scaled_prior = d.const_app(p.sum_range, &[scaled, j]);
            let end = cadd(d, p, scaled_prior, w_fj);
            let refl_wfj = d.lemma(p.equiv_refl, &[w_fj]);
            let h2 = d.lemma(
                p.add_congr,
                &[w_prior, scaled_prior, w_fj, w_fj, ih, refl_wfj],
            );

            echain(d, p, start, &[(distributed, h1), (end, h2)])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_f = d.pi_fv(f_fv, fn_ty, over_n);
        d.pi_fv(w_fv, carrier, over_f)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_f = d.lam_fv(f_fv, fn_ty, over_n);
        d.lam_fv(w_fv, carrier, over_f)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_sum_range,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Nat.lt i n → le (f i) (g i)`, as a Pi type — the `Nat`-bounded pointwise
/// hypothesis [`declare_sum_range_le`] threads through induction, mirroring
/// `nat_prelude/binomial.rs::bounded_pointwise` with `CReal.le` in place of
/// `Eq Nat`.
fn bounded_le_pointwise(
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
    let leq = cle(d, p, fi, gi);
    let body = d.arrow(hyp, leq);
    d.pi_fv(i_fv, nat, body)
}

/// `CReal.sumRange_le : ∀ f g n, (∀ i, Nat.lt i n → le (f i) (g i)) → le
/// (sumRange f n) (sumRange g n)` — monotonicity of a finite sum, with the
/// pointwise hypothesis restricted to indices below the bound, mirroring
/// `Nat.sumRange_congr_lt`'s hypothesis-threading shape
/// (`nat_prelude/binomial.rs::declare_sum_range_congr_lt`) promoted from `Eq`
/// to `CReal.le`.
fn declare_sum_range_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_le_pointwise(d, p, f, g, x);
        let lhs = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.const_app(p.sum_range, &[g, x]);
        let conclusion = cle(d, p, lhs, rhs);
        d.arrow(hyp, conclusion)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = bounded_le_pointwise(d, p, f, g, zero);
            let h_fv = d.fresh_fvar();
            let zero_c = czero(d, p);
            let body = d.lemma(p.le_refl, &[zero_c]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_le_pointwise(d, p, f, g, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // h_lt_j : ∀ i, Nat.lt i j → le (f i) (g i), weakened from `h`.
            let h_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let nat_p = d.prelude();
                let le_succ_j = d.lemma(nat_p.le_succ, &[j]);
                let lifted = d.lemma(nat_p.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let nat_p = d.prelude();
            let lt_j_sj = d.lemma(nat_p.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let f_prior = d.const_app(p.sum_range, &[f, j]);
            let g_prior = d.const_app(p.sum_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let body = d.lemma(p.add_le_add, &[f_prior, g_prior, fj, gj, sub1, sub2]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.monotone_of_le_succ : ∀ f, (∀ n, le (f n) (f (Nat.succ n))) → ∀ a
/// b, Nat.le a b → le (f a) (f b)` — the `CReal`-valued analogue of
/// `Nat.monotone_of_le_succ` (`nat_prelude/order.rs::declare_order`),
/// identical proof shape: eliminate the `Nat.le a b` derivation through
/// `Nat.le`'s own recursor (accessed via [`crate::nat_prelude::NatOps::prelude`]'s
/// `le_rec`) into a `CReal.le`-valued motive — a `Prop`-into-`Prop`
/// elimination, so this never touches `Exists.rec`'s data-elimination
/// restriction — with [`CRealPrelude::le_refl`]/[`CRealPrelude::le_trans`]
/// standing in for `Nat`'s own `le_refl`/`le_trans`.
fn declare_mono_of_le_succ(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let adjacent_fv = d.fresh_fvar();
    let adjacent = d.kernel().fvar(adjacent_fv);
    let adjacent_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_n = d.apply(f, &[n]);
        let sn = d.succ(n);
        let fn_sn = d.apply(f, &[sn]);
        let body = cle(d, p, fn_n, fn_sn);
        d.pi_fv(n_fv, nat, body)
    };
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.le(a, b);
    let fa = d.apply(f, &[a]);
    let fb = d.apply(f, &[b]);
    let conclusion = cle(d, p, fa, fb);

    let anon = d.anon_name();
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hx_ty = d.le(a, x);
        let fx = d.apply(f, &[x]);
        let body = cle(d, p, fa, fx);
        let inner = d.kernel().lam(anon, hx_ty, body, BinderInfo::Default);
        d.lam_fv(x_fv, nat, inner)
    };
    let minor_refl = d.lemma(p.le_refl, &[fa]);
    let minor_step = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hx_fv = d.fresh_fvar();
        let hx_ty = d.le(a, x);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fx = d.apply(f, &[x]);
        let sx = d.succ(x);
        let fsx = d.apply(f, &[sx]);
        let ih_ty = cle(d, p, fa, fx);
        let adjacent_x = d.apply(adjacent, &[x]);
        let body = d.lemma(p.le_trans, &[fa, fx, fsx, ih, adjacent_x]);
        let with_ih = d.lam_fv(ih_fv, ih_ty, body);
        let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
        d.lam_fv(x_fv, nat, with_hx)
    };
    let np = d.prelude();
    let proof = d.const_app(np.le_rec, &[a, motive, minor_refl, minor_step, b, h]);

    let ty = {
        let out = d.kernel().pi(anon, h_ty, conclusion, BinderInfo::Default);
        let out = d.pi_fv(b_fv, nat, out);
        let out = d.pi_fv(a_fv, nat, out);
        let out = d.pi_fv(adjacent_fv, adjacent_ty, out);
        d.pi_fv(f_fv, fn_ty, out)
    };
    let value = {
        let out = d.lam_fv(h_fv, h_ty, proof);
        let out = d.lam_fv(b_fv, nat, out);
        let out = d.lam_fv(a_fv, nat, out);
        let out = d.lam_fv(adjacent_fv, adjacent_ty, out);
        d.lam_fv(f_fv, fn_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mono_of_le_succ,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_mono_outer : ∀ f, (∀ i, le zero (f i)) → ∀ m n, Nat.le m n
/// → le (sumRange f m) (sumRange f n)` — monotonicity of a finite sum in the
/// **outer** index (the summation bound), for a pointwise-nonnegative
/// summand. Distinct in kind from [`declare_sum_range_le`], which compares
/// two *different* summands at the *same* bound: this is genuinely new
/// content, since `CReal.le` is defined only on `CReal` and nothing in
/// `creal/monotone.rs` compares a bare `Nat`-indexed `CReal` sequence across
/// two different outer indices (only same-index Cauchy/regularity facts, or
/// derivative-driven monotonicity of a continuous `CReal → CReal` function).
///
/// Built by applying [`declare_mono_of_le_succ`]'s `CReal.monotone_of_le_succ`
/// to `sumRange f`, with the adjacent step `le (sumRange f n) (sumRange f
/// (Nat.succ n))` proved from `sumRange_succ`'s own defeq (`sumRange f (succ
/// n) ≡ add (sumRange f n) (f n)`) plus the shift-by-a-nonneg-summand
/// argument `x ≤ add x w` from `w ≥ 0` (`add_le_add` against `add x zero`,
/// rewritten through `add_zero` via `le_congr` — the same three-line shape
/// `creal/monotone.rs`'s private `shift_le_of_nonneg` builds, re-derived here
/// since that helper is not `pub(super)`).
fn declare_sum_range_mono_outer(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let hnn_fv = d.fresh_fvar();
    let hnn = d.kernel().fvar(hnn_fv);
    let hnn_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let zero_c = czero(d, p);
        let fi = d.apply(f, &[i]);
        let body = cle(d, p, zero_c, fi);
        d.pi_fv(i_fv, nat, body)
    };

    // sum_f := fun k => sumRange f k, eta-expanded so `monotone_of_le_succ`
    // (stated over an arbitrary `Nat -> CReal`) applies to it directly.
    let sum_f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.sum_range, &[f, k]);
        d.lam_fv(k_fv, nat, body)
    };

    // adjacent : ∀ n, le (sumRange f n) (sumRange f (succ n)) -- the RHS is
    // defeq to `add (sumRange f n) (f n)` via `sumRange_succ`'s own
    // ι-reduction, so the term built below (of that exact type) already
    // type-checks against the Pi `mono_of_le_succ` expects for `sum_f`.
    let adjacent = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sum_f_n = d.const_app(p.sum_range, &[f, n]);
        let f_n = d.apply(f, &[n]);
        let hnn_n = d.apply(hnn, &[n]);
        let zero_c = czero(d, p);
        let refl_x = d.lemma(p.le_refl, &[sum_f_n]);
        let grown = d.lemma(
            p.add_le_add,
            &[sum_f_n, sum_f_n, zero_c, f_n, refl_x, hnn_n],
        );
        let padded = cadd(d, p, sum_f_n, zero_c);
        let target = cadd(d, p, sum_f_n, f_n);
        let trim = d.lemma(p.add_zero, &[sum_f_n]);
        let refl_target = d.lemma(p.equiv_refl, &[target]);
        let body = d.lemma(
            p.le_congr,
            &[padded, sum_f_n, target, target, trim, refl_target, grown],
        );
        d.lam_fv(n_fv, nat, body)
    };

    let mono = d.const_app(p.mono_of_le_succ, &[sum_f, adjacent]);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hmn_fv = d.fresh_fvar();
    let hmn = d.kernel().fvar(hmn_fv);
    let hmn_ty = d.le(m, n);
    let applied = d.apply(mono, &[m, n, hmn]);

    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let sum_f_n = d.const_app(p.sum_range, &[f, n]);
    let conclusion = cle(d, p, sum_f_m, sum_f_n);

    let ty = {
        let anon = d.anon_name();
        let out = d.kernel().pi(anon, hmn_ty, conclusion, BinderInfo::Default);
        let out = d.pi_fv(n_fv, nat, out);
        let out = d.pi_fv(m_fv, nat, out);
        let out = d.arrow(hnn_ty, out);
        d.pi_fv(f_fv, fn_ty, out)
    };
    let value = {
        let out = d.lam_fv(hmn_fv, hmn_ty, applied);
        let out = d.lam_fv(n_fv, nat, out);
        let out = d.lam_fv(m_fv, nat, out);
        let out = d.lam_fv(hnn_fv, hnn_ty, out);
        d.lam_fv(f_fv, fn_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_mono_outer,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.abs_sumRange_le : ∀ f n, le (abs (sumRange f n)) (sumRange (fun k
/// => abs (f k)) n)` — the triangle inequality for finite sums, `|Σf| ≤
/// Σ|f|`. Induction on `n`, closing each step with [`abs_add_le`] chained
/// against the inductive hypothesis via [`CRealPrelude::add_le_add`] and
/// [`CRealPrelude::le_trans`].
fn declare_abs_sum_range_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let absf_fn = |d: &mut IntDev<'_>, f: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = cabs(d, p, fi);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sf = d.const_app(p.sum_range, &[f, x]);
        let lhs = cabs(d, p, sf);
        let absf = absf_fn(d, f);
        let rhs = d.const_app(p.sum_range, &[absf, x]);
        cle(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_c = czero(d, p);
            let le_refl_zero = d.lemma(p.le_refl, &[zero_c]);
            let nz_equiv = neg_zero_equiv(d, p);
            let nz = cneg(d, p, zero_c);
            let le_nz = d.lemma(p.le_of_equiv, &[nz, zero_c, nz_equiv]);
            d.lemma(p.abs_le, &[zero_c, zero_c, le_refl_zero, le_nz])
        },
        &|d, j, ih| {
            let sf_j = d.const_app(p.sum_range, &[f, j]);
            let fj = d.apply(f, &[j]);
            let absf = absf_fn(d, f);
            let saf_j = d.const_app(p.sum_range, &[absf, j]);
            let abs_fj = cabs(d, p, fj);
            let abs_sf_j = cabs(d, p, sf_j);

            let sf_plus_fj = cadd(d, p, sf_j, fj);
            let start = cabs(d, p, sf_plus_fj);
            let mid = cadd(d, p, abs_sf_j, abs_fj);
            let target = cadd(d, p, saf_j, abs_fj);

            let part1 = abs_add_le(d, p, sf_j, fj); // le(start, mid)
            let refl_abs_fj = d.lemma(p.le_refl, &[abs_fj]);
            let part2 = d.lemma(
                p.add_le_add,
                &[abs_sf_j, saf_j, abs_fj, abs_fj, ih, refl_abs_fj],
            ); // le(mid, target)

            d.lemma(p.le_trans, &[start, mid, target, part1, part2])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.abs_sum_range_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_telescope : ∀ f n, Equiv (sumRange (fun k => add (f (succ
/// k)) (neg (f k))) n) (add (f n) (neg (f Nat.zero)))` — `Σ_{k<n} (f(k+1) −
/// f k) ~ f n − f 0`. Induction on `n`: the base case is `symm add_neg`; the
/// successor case rewrites the inductive hypothesis into the accumulated sum
/// via `add_congr`, then closes with [`cancel_left`].
fn declare_sum_range_telescope(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let step_fn = |d: &mut IntDev<'_>, f: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let f_sk = d.apply(f, &[sk]);
        let f_k = d.apply(f, &[k]);
        let neg_fk = cneg(d, p, f_k);
        let body = cadd(d, p, f_sk, neg_fk);
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, body)
    };

    let zero_n = d.zero();
    let f0 = d.apply(f, &[zero_n]);
    let neg_f0 = cneg(d, p, f0);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let g = step_fn(d, f);
        let lhs = d.const_app(p.sum_range, &[g, x]);
        let fx = d.apply(f, &[x]);
        let rhs = cadd(d, p, fx, neg_f0);
        equiv(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let target = cadd(d, p, f0, neg_f0);
            let zero_c = czero(d, p);
            let h = d.lemma(p.add_neg, &[f0]); // Equiv target zero
            d.lemma(p.equiv_symm, &[target, zero_c, h])
        },
        &|d, j, ih| {
            // ih : Equiv (sumRange g j) (add (f j) (neg (f 0)))
            let fj = d.apply(f, &[j]);
            let neg_fj = cneg(d, p, fj);
            let sj = d.succ(j);
            let fsj = d.apply(f, &[sj]);
            let g = step_fn(d, f);
            let sum_gj = d.const_app(p.sum_range, &[g, j]);
            let gj = cadd(d, p, fsj, neg_fj); // = g j, up to beta

            let start = cadd(d, p, sum_gj, gj); // = sumRange g (succ j), up to iota

            let fj_negf0 = cadd(d, p, fj, neg_f0);
            let refl_gj = d.lemma(p.equiv_refl, &[gj]);
            let s1 = cadd(d, p, fj_negf0, gj);
            let h1 = d.lemma(p.add_congr, &[sum_gj, fj_negf0, gj, gj, ih, refl_gj]);

            // s1 = (fj + neg_f0) + (fsj + neg_fj) ~ fsj + neg_f0
            let (target, h2) = cancel_left(d, p, fj, neg_f0, fsj);

            echain(d, p, start, &[(s1, h1), (target, h2)])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_telescope,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_split : ∀ f m n, Equiv (sumRange f (add m n)) (add
/// (sumRange f m) (sumRange (fun k => f (add m k)) n))`. Induction on `n`;
/// both cases close purely by `Nat.add`'s own iota-reduction (`add m
/// Nat.zero ≡ m`, `add m (succ j) ≡ succ (add m j)`) plus one
/// `add_zero`/`add_assoc` respectively — no new rational estimate, and the
/// lemma every "tail of a partial sum" argument opens with.
fn declare_sum_range_split(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_add = d.prelude().add;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sum_f_m = d.const_app(p.sum_range, &[f, m]);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let m_plus_x = d.const_app(nat_add, &[m, x]);
        let lhs = d.const_app(p.sum_range, &[f, m_plus_x]);
        let h = shifted_fn(d, m, f);
        let sum_h_x = d.const_app(p.sum_range, &[h, x]);
        let rhs = cadd(d, p, sum_f_m, sum_h_x);
        equiv(d, p, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_c = czero(d, p);
            let padded = cadd(d, p, sum_f_m, zero_c);
            let h = d.lemma(p.add_zero, &[sum_f_m]); // Equiv padded sum_f_m
            d.lemma(p.equiv_symm, &[padded, sum_f_m, h])
        },
        &|d, j, ih| {
            // ih : Equiv (sumRange f (add m j)) (add sum_f_m (sumRange h j))
            let h = shifted_fn(d, m, f);
            let sum_h_j = d.const_app(p.sum_range, &[h, j]);
            let m_plus_j = d.const_app(nat_add, &[m, j]);
            let fmj = d.apply(f, &[m_plus_j]); // = f (add m j) = h j, up to beta

            let sum_f_mj = d.const_app(p.sum_range, &[f, m_plus_j]);
            let start = cadd(d, p, sum_f_mj, fmj); // = sumRange f (add m (succ j)), up to iota

            let rhs_prior = cadd(d, p, sum_f_m, sum_h_j);
            let refl_fmj = d.lemma(p.equiv_refl, &[fmj]);
            let s1 = cadd(d, p, rhs_prior, fmj);
            let h1 = d.lemma(p.add_congr, &[sum_f_mj, rhs_prior, fmj, fmj, ih, refl_fmj]);

            let sum_h_j_plus_fmj = cadd(d, p, sum_h_j, fmj);
            let target = cadd(d, p, sum_f_m, sum_h_j_plus_fmj);
            let h2 = d.lemma(p.add_assoc, &[sum_f_m, sum_h_j, fmj]);

            echain(d, p, start, &[(s1, h1), (target, h2)])
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        d.pi_fv(f_fv, fn_ty, over_m)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        d.lam_fv(f_fv, fn_ty, over_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_split,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_tail_le : ∀ f g m n, (∀ k, le (abs (f k)) (g k)) → le (abs
/// (add (sumRange f (add m n)) (neg (sumRange f m)))) (add (sumRange g (add m
/// n)) (neg (sumRange g m)))` — **the comparison test**: an `m`-to-`m+n` tail
/// of `f`'s partial sums is bounded by the corresponding tail of `g`'s,
/// whenever `f` is pointwise bounded by `g` in absolute value.
///
/// Not stated through `CReal.Cauchy` — see the module documentation for why.
/// Both tails are rewritten to a shifted partial sum via [`declare_sum_range_split`]
/// and [`cancel_right`] (`(sumRange f m + sumRange h n) + (-(sumRange f m)) ~
/// sumRange h n`), then chained through [`CRealPrelude::abs_congr`],
/// [`CRealPrelude::abs_sum_range_le`] and [`CRealPrelude::sum_range_le`] (the
/// pointwise hypothesis applied at the shifted index) with three
/// [`CRealPrelude::le_trans`] steps.
fn declare_sum_range_tail_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_add = d.prelude().add;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pointwise_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let abs_fk = cabs(d, p, fk);
        let leq = cle(d, p, abs_fk, gk);
        d.pi_fv(k_fv, nat, leq)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let m_plus_n = d.const_app(nat_add, &[m, n]);
    let sum_f_mn = d.const_app(p.sum_range, &[f, m_plus_n]);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let neg_sum_f_m = cneg(d, p, sum_f_m);
    let tail_f = cadd(d, p, sum_f_mn, neg_sum_f_m);

    let sum_g_mn = d.const_app(p.sum_range, &[g, m_plus_n]);
    let sum_g_m = d.const_app(p.sum_range, &[g, m]);
    let neg_sum_g_m = cneg(d, p, sum_g_m);
    let tail_g = cadd(d, p, sum_g_mn, neg_sum_g_m);

    let abs_tail_f = cabs(d, p, tail_f);
    let target = cle(d, p, abs_tail_f, tail_g);

    let h_f = shifted_fn(d, m, f);
    let h_g = shifted_fn(d, m, g);
    let sum_hf_n = d.const_app(p.sum_range, &[h_f, n]);
    let sum_hg_n = d.const_app(p.sum_range, &[h_g, n]);

    // tail_f ~ sum_hf_n, via sumRange_split[f,m,n] + cancel_right.
    let split_f = d.lemma(p.sum_range_split, &[f, m, n]); // Equiv sum_f_mn (add sum_f_m sum_hf_n)
    let sum_f_m_plus_hf = cadd(d, p, sum_f_m, sum_hf_n);
    let refl_neg_f = d.lemma(p.equiv_refl, &[neg_sum_f_m]);
    let step_a = d.lemma(
        p.add_congr,
        &[
            sum_f_mn,
            sum_f_m_plus_hf,
            neg_sum_f_m,
            neg_sum_f_m,
            split_f,
            refl_neg_f,
        ],
    ); // Equiv tail_f (add sum_f_m_plus_hf neg_sum_f_m)
    let middle_f = cadd(d, p, sum_f_m_plus_hf, neg_sum_f_m);
    let cancel_f = cancel_right(d, p, sum_f_m, sum_hf_n); // Equiv middle_f sum_hf_n
    let tail_f_equiv = d.lemma(
        p.equiv_trans,
        &[tail_f, middle_f, sum_hf_n, step_a, cancel_f],
    );

    // tail_g ~ sum_hg_n, identically.
    let split_g = d.lemma(p.sum_range_split, &[g, m, n]);
    let sum_g_m_plus_hg = cadd(d, p, sum_g_m, sum_hg_n);
    let refl_neg_g = d.lemma(p.equiv_refl, &[neg_sum_g_m]);
    let step_b = d.lemma(
        p.add_congr,
        &[
            sum_g_mn,
            sum_g_m_plus_hg,
            neg_sum_g_m,
            neg_sum_g_m,
            split_g,
            refl_neg_g,
        ],
    );
    let middle_g = cadd(d, p, sum_g_m_plus_hg, neg_sum_g_m);
    let cancel_g = cancel_right(d, p, sum_g_m, sum_hg_n); // Equiv middle_g sum_hg_n
    let tail_g_equiv = d.lemma(
        p.equiv_trans,
        &[tail_g, middle_g, sum_hg_n, step_b, cancel_g],
    );

    // r1 : le abs_tail_f (abs sum_hf_n)
    let abs_sum_hf_n = cabs(d, p, sum_hf_n);
    let abs_congr_f = d.lemma(p.abs_congr, &[tail_f, sum_hf_n, tail_f_equiv]);
    let r1 = d.lemma(p.le_of_equiv, &[abs_tail_f, abs_sum_hf_n, abs_congr_f]);

    // r2 : le (abs sum_hf_n) (sumRange |h_f| n)
    let absf_hf = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hfi = d.apply(h_f, &[i]);
        let body = cabs(d, p, hfi);
        d.lam_fv(i_fv, nat, body)
    };
    let sum_absf_hf_n = d.const_app(p.sum_range, &[absf_hf, n]);
    let r2 = d.lemma(p.abs_sum_range_le, &[h_f, n]);

    // r3 : le (sumRange |h_f| n) sum_hg_n, via sumRange_le, pointwise from `hyp`.
    let pointwise_proof = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt_fv = d.fresh_fvar();
        let lt_ty = d.lt(i, n);
        let mi = d.const_app(nat_add, &[m, i]);
        let applied = d.apply(hyp, &[mi]); // le (abs (f (add m i))) (g (add m i))
        let inner = d.lam_fv(lt_fv, lt_ty, applied);
        d.lam_fv(i_fv, nat, inner)
    };
    let r3 = d.lemma(p.sum_range_le, &[absf_hf, h_g, n, pointwise_proof]);

    // r4 : le sum_hg_n tail_g
    let tail_g_symm = d.lemma(p.equiv_symm, &[tail_g, sum_hg_n, tail_g_equiv]);
    let r4 = d.lemma(p.le_of_equiv, &[sum_hg_n, tail_g, tail_g_symm]);

    let c1 = d.lemma(
        p.le_trans,
        &[abs_tail_f, abs_sum_hf_n, sum_absf_hf_n, r1, r2],
    );
    let c2 = d.lemma(p.le_trans, &[abs_tail_f, sum_absf_hf_n, sum_hg_n, c1, r3]);
    let proof_body = d.lemma(p.le_trans, &[abs_tail_f, sum_hg_n, tail_g, c2, r4]);

    let ty = {
        let after_hyp = d.arrow(pointwise_ty, target);
        let over_n = d.pi_fv(n_fv, nat, after_hyp);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_g = d.pi_fv(g_fv, fn_ty, over_m);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_hyp = d.lam_fv(hyp_fv, pointwise_ty, proof_body);
        let over_n = d.lam_fv(n_fv, nat, with_hyp);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_g = d.lam_fv(g_fv, fn_ty, over_m);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_tail_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// From `Rat.le (Rat.sub u v) w` and `Rat.le (Rat.sub (Rat.neg u) v) w`,
/// derive `CReal.Within u (Rat.add v w)` — the "within-swap via `neg_sub`"
/// helper the module documentation names as the first piece to land. It is
/// what turns the two one-sided `CReal.le`-unfolded bounds
/// (`le_trans le_abs_self sum_range_tail_le` /
/// `le_trans neg_le_abs sum_range_tail_le`, each applied at a shared index)
/// into the single `Within` bound the outer telescope's middle leg needs,
/// rather than one `abs_le` call — `abs_le`'s hypothesis shape does not
/// survive sampling at an index.
///
/// Modelled on [`super::weaken`]'s own `neg_le_neg` + rewrite pattern: the
/// upper half is `le_of_sub_le` outright; the lower half is `le_of_sub_le`
/// on `h2`, then `neg_le_neg` to flip it, then one `neg_neg` rewrite to
/// strip the resulting double negation back off `u` (`Rat`'s `neg_neg` is a
/// proved theorem, not a computation, so this rewrite is not optional the
/// way it would be over `CReal`'s ι-reducing `neg`).
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

    // upper : le u vw
    let upper = d.lemma(rat.le_of_sub_le, &[u, v, w, h1]);

    // lower_neg : le (neg u) vw
    let neg_u = rneg(d, u);
    let lower_neg = d.lemma(rat.le_of_sub_le, &[neg_u, v, w, h2]);

    // flipped : le (neg vw) (neg (neg u))
    let neg_vw = rneg(d, vw);
    let neg_neg_u = rneg(d, neg_u);
    let flipped = d.lemma(rat.neg_le_neg, &[neg_u, vw, lower_neg]);

    // nn : Eq (neg (neg u)) u; lower : le (neg vw) u.
    let nn = d.lemma(rat.neg_neg, &[u]);
    let lower = rat_eq_rewrite(d, neg_neg_u, u, nn, flipped, &|d, t| rle(d, rat, neg_vw, t));

    let lower_ty = rle(d, rat, neg_vw, u);
    let upper_ty = rle(d, rat, u, vw);
    and_intro(d, p, lower_ty, upper_ty, lower, upper)
}

/// `CReal.sumRange_tail_within`. See the field documentation
/// ([`super::CRealPrelude::sum_range_tail_within`]) and this module's own
/// documentation for what this theorem is and is not: the middle leg the
/// outer telescope needs, not the telescope itself.
///
/// Reuses [`declare_sum_range_tail_le`]'s own `tail_f`/`tail_g`
/// construction verbatim, chains `le_abs_self`/`neg_le_abs` through
/// `le_trans` against that theorem's conclusion to get the two one-sided
/// `CReal.le` facts, applies each at the tail's own index `add m n`
/// (**not** at a further-shifted index — `CReal.add`'s own shift already
/// lands both `tail_f`'s and `tail_g`'s samples at `shift (add m n)`
/// automatically, by ι-reduction, once sampled at `add m n`), and closes
/// with [`within_of_tail_le`].
fn declare_sum_range_tail_within(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_add = d.prelude().add;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pointwise_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let abs_fk = cabs(d, p, fk);
        let leq = cle(d, p, abs_fk, gk);
        d.pi_fv(k_fv, nat, leq)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let m_plus_n = d.const_app(nat_add, &[m, n]);
    let sum_f_mn = d.const_app(p.sum_range, &[f, m_plus_n]);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let neg_sum_f_m = cneg(d, p, sum_f_m);
    let tail_f = cadd(d, p, sum_f_mn, neg_sum_f_m);

    let sum_g_mn = d.const_app(p.sum_range, &[g, m_plus_n]);
    let sum_g_m = d.const_app(p.sum_range, &[g, m]);
    let neg_sum_g_m = cneg(d, p, sum_g_m);
    let tail_g = cadd(d, p, sum_g_mn, neg_sum_g_m);

    // tail_le : CReal.le (abs tail_f) tail_g
    let tail_le = d.lemma(p.sum_range_tail_le, &[f, g, m, n, hyp]);
    let abs_tail_f = cabs(d, p, tail_f);

    // r1 : CReal.le tail_f tail_g
    let le_abs_self_f = d.lemma(p.le_abs_self, &[tail_f]);
    let r1 = d.lemma(
        p.le_trans,
        &[tail_f, abs_tail_f, tail_g, le_abs_self_f, tail_le],
    );

    // r2 : CReal.le (neg tail_f) tail_g
    let neg_tail_f = cneg(d, p, tail_f);
    let neg_le_abs_f = d.lemma(p.neg_le_abs, &[tail_f]);
    let r2 = d.lemma(
        p.le_trans,
        &[neg_tail_f, abs_tail_f, tail_g, neg_le_abs_f, tail_le],
    );

    // Both applied at the tail's own defining index.
    let r1_mn = d.apply(r1, &[m_plus_n]);
    let r2_mn = d.apply(r2, &[m_plus_n]);

    let u = sample(d, p, tail_f, m_plus_n);
    let v = sample(d, p, tail_g, m_plus_n);
    let w = div_succ(d, p, 2, m_plus_n);

    let value_body = within_of_tail_le(d, p, u, v, w, r1_mn, r2_mn);

    let ty = {
        let vw = radd(d, v, w);
        let claim = within(d, p, u, vw);
        let after_hyp = d.arrow(pointwise_ty, claim);
        let over_n = d.pi_fv(n_fv, nat, after_hyp);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_g = d.pi_fv(g_fv, fn_ty, over_m);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_hyp = d.lam_fv(hyp_fv, pointwise_ty, value_body);
        let over_n = d.lam_fv(n_fv, nat, with_hyp);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_g = d.lam_fv(g_fv, fn_ty, over_m);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_tail_within,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_tail_within_le`. See the field documentation
/// ([`super::CRealPrelude::sum_range_tail_within_le`]) for the statement and
/// this module's documentation for why it exists: lifting
/// [`declare_sum_range_tail_within`]'s ordered-pair form `(m, add m n)` to an
/// arbitrary pair `(a, b)` with `a ≤ b` is the "Nat.le_total case split" the
/// module documentation lists as one of the four remaining pieces.
///
/// `Nat.le_dest a b hle : Exists (fun k => Eq (add a k) b)`. Applying
/// [`declare_sum_range_tail_within`] at `(a, k)` gives exactly this
/// theorem's target *shape*, but indexed at `add a k` rather than `b`; one
/// `Nat`-equality transport ([`nat_rewrite_prop`]) along the witness
/// `Eq (add a k) b` carries every occurrence of the shared index over to
/// `b`, and [`exists_elim`] discharges the existential.
fn declare_sum_range_tail_within_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_add = d.prelude().add;
    let nat_le_dest = d.prelude().le_dest;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let pointwise_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let abs_fk = cabs(d, p, fk);
        let leq = cle(d, p, abs_fk, gk);
        d.pi_fv(k_fv, nat, leq)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let hle_ty = d.le(a, b);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    // `target_at(x)`: the claim with the shared index left as `x`, so it
    // reads directly off `declare_sum_range_tail_within`'s own conclusion
    // shape at `x := add a k`, and is this theorem's conclusion at `x := b`.
    let sum_f_a = d.const_app(p.sum_range, &[f, a]);
    let neg_sum_f_a = cneg(d, p, sum_f_a);
    let sum_g_a = d.const_app(p.sum_range, &[g, a]);
    let neg_sum_g_a = cneg(d, p, sum_g_a);
    let target_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sum_f_x = d.const_app(p.sum_range, &[f, x]);
        let tail_f_x = cadd(d, p, sum_f_x, neg_sum_f_a);
        let u = sample(d, p, tail_f_x, x);
        let sum_g_x = d.const_app(p.sum_range, &[g, x]);
        let tail_g_x = cadd(d, p, sum_g_x, neg_sum_g_a);
        let v = sample(d, p, tail_g_x, x);
        let w = div_succ(d, p, 2, x);
        let vw = radd(d, v, w);
        within(d, p, u, vw)
    };
    let target = target_at(d, b);

    // pred := λ k, Eq Nat (add a k) b.
    let pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sum = d.const_app(nat_add, &[a, k]);
        let body = d.eq(sum, b);
        d.lam_fv(k_fv, nat, body)
    };

    let represented = d.const_app(nat_le_dest, &[a, b, hle]);

    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let a_plus_k = d.const_app(nat_add, &[a, k]);
        let e_ty = d.eq(a_plus_k, b);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        // body_at_ak : target_at(add a k) -- exactly
        // `sum_range_tail_within f g hyp a k`'s own conclusion.
        let body_at_ak = d.lemma(p.sum_range_tail_within, &[f, g, a, k, hyp]);
        let rewritten = nat_rewrite_prop(d, a_plus_k, b, e, body_at_ak, &|d, x| target_at(d, x));

        let with_e = d.lam_fv(e_fv, e_ty, rewritten);
        d.lam_fv(k_fv, nat, with_e)
    };

    let proof_body = exists_elim(d, pred, target, represented, minor);

    let ty = {
        let after_hle = d.arrow(hle_ty, target);
        let after_hyp = d.arrow(pointwise_ty, after_hle);
        let over_b = d.pi_fv(b_fv, nat, after_hyp);
        let over_a = d.pi_fv(a_fv, nat, over_b);
        let over_g = d.pi_fv(g_fv, fn_ty, over_a);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, proof_body);
        let with_hyp = d.lam_fv(hyp_fv, pointwise_ty, with_hle);
        let over_b = d.lam_fv(b_fv, nat, with_hyp);
        let over_a = d.lam_fv(a_fv, nat, over_b);
        let over_g = d.lam_fv(g_fv, fn_ty, over_a);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_tail_within_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.natDivSucc k j`, with `k` a **variable** rather than a literal —
/// [`div_succ`](super::div_succ) only takes a `u32`, and the Cauchy witness
/// below needs the modulus at its own free witness `K`.
fn div_succ_var(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, j])
}

/// From `Within (x−y) bxy`, `Within (y−z) byz`, `Within (z−w) bzw`, derive
/// `Within (x−w) ((bxy+byz)+bzw)` — two applications of `Rat.sub_add_sub`
/// (`(a−b)+(b−c) ~ a−c`), [`declare_limit_dist`](super::completeness::declare_limit_dist)'s
/// own two-leg chaining shape one leg longer. Needs no `Rat.neg`/`bounds_neg`
/// anywhere, unlike
/// [`declare_converges_cauchy`](super::convergence)'s `regroup_middle_four`:
/// the three legs here already share consecutive endpoints (`x,y` / `y,z` /
/// `z,w`) in the right order, so each combining step is a direct
/// `sub_add_sub` rewrite rather than a four-term regrouping.
pub(super) fn chain_within3(
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

/// `CReal.sumRange_tail_cauchy_within` — the **inner telescope** the module
/// documentation's "Cauchy-shape conversion" section names, and
/// [`CRealPrelude::sum_range_tail_within`]'s own doc comment flags as unbuilt:
/// bounding `sumRange_tail_within`'s `g`-side rational sample `seq (add
/// (sumRange g (add m n)) (neg (sumRange g m))) (add m n)` through a Cauchy
/// witness for `sumRange g`, rather than through `sum_range_tail_le` (which
/// is the machinery that reaches this quantity in the first place, not what
/// bounds it).
///
/// Takes the **witnessed** form of `CReal.Cauchy (sumRange g)` directly — `∀
/// pp qq, Within (seq (sumRange g pp) pp − seq (sumRange g qq) qq)
/// (natDivSucc K pp + natDivSucc K qq)`, for an explicit `K` — rather than the
/// existentially-quantified `CReal.Cauchy (sumRange g)` itself, so this
/// theorem needs no `Exists.rec` motive of its own. Extracting `K` from an
/// actual `Cauchy` hypothesis is left to whichever future piece (the outer
/// telescope, or the assembly of `sumRange_cauchy_of_dominated` itself)
/// consumes this one — exactly the granularity
/// [`declare_converges_cauchy`](super::convergence)'s own `minor` closure
/// already works at, one module over.
///
/// At the shared index `t := shift (add m n)`, `q := add m n`: writing `X :=
/// seq (sumRange g q) t`, `Y := seq (sumRange g q) q`, `Z := seq (sumRange g
/// m) m`, `W := seq (sumRange g m) t`, the target `seq (add (sumRange g q)
/// (neg (sumRange g m))) q` is **defeq** to `X − W` (`CReal.add`'s own `mk
/// (fun n => …) _` representative plus `CReal.neg`'s, both bare `Nat → CReal`
/// projections with no `Nat.rec` in the way — the same ι/β argument
/// [`declare_sum_range_seq_equations`]'s own doc comment gives for the
/// simpler `add`-only case), so no separate `Eq` lemma is declared for it;
/// the kernel accepts [`chain_within3`]'s output at that type directly. The
/// three legs: `X − Y` via [`CRealPrelude::regular`] at `(sumRange g q, t,
/// q)`; `Y − Z` via the witnessed hypothesis applied at `(q, m)`; `Z − W` via
/// [`CRealPrelude::regular`] at `(sumRange g m, m, t)`.
fn declare_sum_range_tail_cauchy_within(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_add = d.prelude().add;

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    // hyp_ty : ∀ pp qq, Within (seq (sumRange g pp) pp − seq (sumRange g qq)
    //                            qq) (natDivSucc k pp + natDivSucc k qq)
    let hyp_ty = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);
        let sum_pp = d.const_app(p.sum_range, &[g, pp]);
        let sum_qq = d.const_app(p.sum_range, &[g, qq]);
        let left = sample(d, p, sum_pp, pp);
        let right = sample(d, p, sum_qq, qq);
        let diff = rsub(d, rat, left, right);
        let bpp = div_succ_var(d, p, k, pp);
        let bqq = div_succ_var(d, p, k, qq);
        let bound = radd(d, bpp, bqq);
        let claim = within(d, p, diff, bound);
        let over_qq = d.pi_fv(qq_fv, nat, claim);
        d.pi_fv(pp_fv, nat, over_qq)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let q = d.const_app(nat_add, &[m, n]);
    let t = shift(d, q);

    let sum_g_q = d.const_app(p.sum_range, &[g, q]);
    let sum_g_m = d.const_app(p.sum_range, &[g, m]);

    let x = sample(d, p, sum_g_q, t);
    let y = sample(d, p, sum_g_q, q);
    let z = sample(d, p, sum_g_m, m);
    let w = sample(d, p, sum_g_m, t);

    // leg1 : Within (X - Y) (modulus t q).
    let leg1 = d.lemma(p.regular, &[sum_g_q, t, q]);
    let b1 = modulus(d, p, t, q);

    // leg2 : Within (Y - Z) (natDivSucc k q + natDivSucc k m), via `hyp q m`.
    let leg2 = d.apply(hyp, &[q, m]);
    let b2 = {
        let bq = div_succ_var(d, p, k, q);
        let bm = div_succ_var(d, p, k, m);
        radd(d, bq, bm)
    };

    // leg3 : Within (Z - W) (modulus m t).
    let leg3 = d.lemma(p.regular, &[sum_g_m, m, t]);
    let b3 = modulus(d, p, m, t);

    let telescoped = chain_within3(d, p, x, y, z, w, b1, b2, b3, leg1, leg2, leg3);
    let total_bound = {
        let b12 = radd(d, b1, b2);
        radd(d, b12, b3)
    };

    // tail_sample is defeq to (x - w); see the doc comment above.
    let neg_sum_g_m = cneg(d, p, sum_g_m);
    let tail_g = cadd(d, p, sum_g_q, neg_sum_g_m);
    let tail_sample = sample(d, p, tail_g, q);

    let ty = {
        let claim = within(d, p, tail_sample, total_bound);
        let after_hyp = d.arrow(hyp_ty, claim);
        let over_n = d.pi_fv(n_fv, nat, after_hyp);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_k = d.pi_fv(k_fv, nat, over_m);
        d.pi_fv(g_fv, fn_ty, over_k)
    };
    let value = {
        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, telescoped);
        let over_n = d.lam_fv(n_fv, nat, with_hyp);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_k = d.lam_fv(k_fv, nat, over_m);
        d.lam_fv(g_fv, fn_ty, over_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_tail_cauchy_within,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_tail_within_cauchy` — the **outer telescope**. See
/// [`CRealPrelude::sum_range_tail_within_cauchy`]'s own doc comment for the
/// statement and the module documentation's "Cauchy-shape conversion"
/// section for the construction this closes.
///
/// Combines [`declare_sum_range_tail_within`]'s conclusion `Within u (v+w)`
/// with [`declare_sum_range_tail_cauchy_within`]'s conclusion `Within v B`
/// (the same `v`, built identically by both from the same `m`, `n` — no
/// transport needed) via [`weaken`]: extract `le v B` from the second
/// conclusion's upper half ([`halves`]), widen it to `le (v+w) (B+w)` with
/// one `Rat.add_le_add` against `Rat.le_refl w`, then widen the first
/// conclusion's own bound along that order. No further telescope is needed
/// — both theorems this one composes already did that work.
fn declare_sum_range_tail_within_cauchy(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_add = d.prelude().add;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pointwise_ty = {
        let kk_fv = d.fresh_fvar();
        let kk = d.kernel().fvar(kk_fv);
        let fk = d.apply(f, &[kk]);
        let gk = d.apply(g, &[kk]);
        let abs_fk = cabs(d, p, fk);
        let leq = cle(d, p, abs_fk, gk);
        d.pi_fv(kk_fv, nat, leq)
    };
    let hyp1_fv = d.fresh_fvar();
    let hyp1 = d.kernel().fvar(hyp1_fv);

    let cauchy_hyp_ty = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);
        let sum_pp = d.const_app(p.sum_range, &[g, pp]);
        let sum_qq = d.const_app(p.sum_range, &[g, qq]);
        let left = sample(d, p, sum_pp, pp);
        let right = sample(d, p, sum_qq, qq);
        let diff = rsub(d, rat, left, right);
        let bpp = div_succ_var(d, p, k, pp);
        let bqq = div_succ_var(d, p, k, qq);
        let bound = radd(d, bpp, bqq);
        let claim = within(d, p, diff, bound);
        let over_qq = d.pi_fv(qq_fv, nat, claim);
        d.pi_fv(pp_fv, nat, over_qq)
    };
    let hyp2_fv = d.fresh_fvar();
    let hyp2 = d.kernel().fvar(hyp2_fv);

    // u := sample tail_f (m+n), v := sample tail_g (m+n), w := div_succ 2 (m+n)
    // -- identical constructions to `declare_sum_range_tail_within`'s own.
    let m_plus_n = d.const_app(nat_add, &[m, n]);
    let sum_f_mn = d.const_app(p.sum_range, &[f, m_plus_n]);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let neg_sum_f_m = cneg(d, p, sum_f_m);
    let tail_f = cadd(d, p, sum_f_mn, neg_sum_f_m);
    let u = sample(d, p, tail_f, m_plus_n);

    let sum_g_mn = d.const_app(p.sum_range, &[g, m_plus_n]);
    let sum_g_m = d.const_app(p.sum_range, &[g, m]);
    let neg_sum_g_m = cneg(d, p, sum_g_m);
    let tail_g = cadd(d, p, sum_g_mn, neg_sum_g_m);
    let v = sample(d, p, tail_g, m_plus_n);

    let w = div_succ(d, p, 2, m_plus_n);

    // within1 : Within u (v+w).
    let within1 = d.lemma(p.sum_range_tail_within, &[f, g, m, n, hyp1]);

    // within2 : Within v total_bound -- `v` here is built identically to
    // `sum_range_tail_cauchy_within`'s own `tail_sample` at the same g, m, n.
    let within2 = d.lemma(p.sum_range_tail_cauchy_within, &[g, k, m, n, hyp2]);

    let q = m_plus_n;
    let t = shift(d, q);
    let b1 = modulus(d, p, t, q);
    let b2 = {
        let bq = div_succ_var(d, p, k, q);
        let bm = div_succ_var(d, p, k, m);
        radd(d, bq, bm)
    };
    let b3 = modulus(d, p, m, t);
    let total_bound = {
        let b12 = radd(d, b1, b2);
        radd(d, b12, b3)
    };

    // order : le (v+w) (total_bound+w), via add_le_add on `le v total_bound`
    // (the upper half of within2) and `le_refl w`.
    let (_, upper_v) = halves(d, p, v, total_bound, within2);
    let refl_w = d.lemma(rat.le_refl, &[w]);
    let order = d.lemma(rat.add_le_add, &[v, total_bound, w, w, upper_v, refl_w]);

    let vw = radd(d, v, w);
    let final_bound = radd(d, total_bound, w);

    let value_body = weaken(d, p, u, vw, final_bound, within1, order);

    let ty = {
        let claim = within(d, p, u, final_bound);
        let after_hyp2 = d.arrow(cauchy_hyp_ty, claim);
        let after_hyp1 = d.arrow(pointwise_ty, after_hyp2);
        let over_n = d.pi_fv(n_fv, nat, after_hyp1);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_k = d.pi_fv(k_fv, nat, over_m);
        let over_g = d.pi_fv(g_fv, fn_ty, over_k);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_hyp2 = d.lam_fv(hyp2_fv, cauchy_hyp_ty, value_body);
        let with_hyp1 = d.lam_fv(hyp1_fv, pointwise_ty, with_hyp2);
        let over_n = d.lam_fv(n_fv, nat, with_hyp1);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_k = d.lam_fv(k_fv, nat, over_m);
        let over_g = d.lam_fv(g_fv, fn_ty, over_k);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_tail_within_cauchy,
        uparams: vec![],
        ty,
        value,
    })
}

/// From `Within (a-b) q`, derive `Within (b-a) q` via `Rat.neg_sub` (`neg
/// (a-b) = b-a`) and `Rat.bounds_neg` (negating a two-sided bound keeps it) —
/// the generic "swap the two sides of a `Within` difference" helper
/// [`dominated_canonical_at`] uses to turn each `CReal.regular` leg (which
/// always bounds "earlier index minus later index") into whichever
/// orientation its three-leg chain needs.
pub(super) fn within_symm(
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

/// The four legs [`dominated_canonical_at`] chains at shared index `x`
/// (`t := shift x`, `m` fixed): `bxy := modulus t x`, `bzw := modulus m t`
/// bracket `byz`, [`declare_sum_range_tail_within_cauchy`]'s own
/// `final_bound` reconstructed identically (same `radd`/`modulus`/
/// `div_succ_var`/`div_succ` calls in the same order) so that theorem's
/// conclusion, applied at `(m, x)`'s defining gap, lands at exactly this
/// `byz` — not merely an equal expression, the same one, which is what lets
/// the kernel accept it in that argument position without an explicit `Eq`
/// rewrite. `total` is their sum, the bound
/// [`declare_sum_range_cauchy_dominated_ordered`]'s `target_at` states.
fn dominated_canonical_legs(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    m: ExprId,
    x: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let t = shift(d, x);
    let bxy = modulus(d, p, t, x);
    let b2 = {
        let bx = div_succ_var(d, p, k, x);
        let bm = div_succ_var(d, p, k, m);
        radd(d, bx, bm)
    };
    let bzw = modulus(d, p, m, t);
    let bxy_b2 = radd(d, bxy, b2);
    let total_bound_g = radd(d, bxy_b2, bzw);
    let w_extra = div_succ(d, p, 2, x);
    let byz = radd(d, total_bound_g, w_extra);
    let bxy_byz = radd(d, bxy, byz);
    let total = radd(d, bxy_byz, bzw);
    (bxy, byz, bzw, total)
}

/// The bound [`declare_sum_range_cauchy_dominated_ordered`]'s `target_at`
/// states at shared index `x` — [`dominated_canonical_legs`]'s `total`.
fn dominated_canonical_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    m: ExprId,
    x: ExprId,
) -> ExprId {
    dominated_canonical_legs(d, p, k, m, x).3
}

/// The canonical-index extraction: from
/// [`CRealPrelude::sum_range_tail_within_cauchy`]'s bound on `f`'s tail
/// sampled at the *shared, shifted* index `t := shift q` (`q := add m gap`)
/// — a bound on `seq (sumRange f q) t − seq (sumRange f m) t` — plus two more
/// `CReal.regular` legs bridging each side of that back to its own
/// **canonical** sample (`seq (sumRange f q) q`, `seq (sumRange f m) m`),
/// derive a bound on `seq (sumRange f q) q − seq (sumRange f m) m` itself:
/// the shape [`CRealPrelude::cauchy`] actually needs, not the shifted-sample
/// shape `sum_range_tail_within_cauchy` supplies.
///
/// Four points, chained `Y → X → W → Z` (`Y := seq (sumRange f q) q`,
/// `X := seq (sumRange f q) t`, `W := seq (sumRange f m) t`,
/// `Z := seq (sumRange f m) m`) via [`chain_within3`], **not** the
/// `X → Y → Z → W` order `sum_range_tail_cauchy_within`'s own inner
/// telescope uses — that telescope's middle leg was a *known* Cauchy
/// witness; here the middle leg (`X − W`) is the *known* quantity
/// (`sum_range_tail_within_cauchy`'s own conclusion, defeq to `X − W` for
/// the same ι/β reason that theorem's own doc comment gives) and `Y − Z` is
/// what is wanted, so the known bound has to sit in the **middle** of the
/// chain rather than at an end — the two `CReal.regular` legs (`Y − X`,
/// `W − Z`) are each a [`within_symm`] flip of the natural
/// `regular`-supplied orientation (`X − Y`, `Z − W`).
fn dominated_canonical_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    g: ExprId,
    k: ExprId,
    m: ExprId,
    gap: ExprId,
    hyp1: ExprId,
    hyp2: ExprId,
) -> ExprId {
    let nat_add = d.prelude().add;
    let q = d.const_app(nat_add, &[m, gap]);
    let t = shift(d, q);

    let tail_cw = d.lemma(
        p.sum_range_tail_within_cauchy,
        &[f, g, k, m, gap, hyp1, hyp2],
    );
    let (bxy, byz, bzw, _total) = dominated_canonical_legs(d, p, k, m, q);

    let sum_f_q = d.const_app(p.sum_range, &[f, q]);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);

    let x_pt = sample(d, p, sum_f_q, t);
    let y_pt = sample(d, p, sum_f_q, q);
    let z_pt = sample(d, p, sum_f_m, m);
    let w_pt = sample(d, p, sum_f_m, t);

    let reg1 = d.lemma(p.regular, &[sum_f_q, t, q]);
    let p_yx = within_symm(d, p, x_pt, y_pt, bxy, reg1);

    let reg2 = d.lemma(p.regular, &[sum_f_m, m, t]);
    let p_wz = within_symm(d, p, z_pt, w_pt, bzw, reg2);

    chain_within3(
        d, p, y_pt, x_pt, w_pt, z_pt, bxy, byz, bzw, p_yx, tail_cw, p_wz,
    )
}

/// `CReal.sumRange_cauchy_dominated_ordered` — the ordered-pair half of
/// wiring `sumRange_tail_within_cauchy` through to `CReal.Cauchy`'s own
/// canonical two-index shape, the gap the module documentation's
/// "Cauchy-shape conversion" section names as unfinished: lifts
/// [`dominated_canonical_at`]'s ordered-pair form `(m, add m gap)` to an
/// arbitrary pair `(a, b)` constrained only by `a ≤ b`, exactly the
/// `Nat.le_dest`-plus-transport technique
/// [`declare_sum_range_tail_within_le`] already used to lift
/// `sum_range_tail_within` the same way — reused here, not re-derived,
/// against a different (canonical-shape, Cauchy-witnessed) payload.
///
/// Selecting between this pair's two orientations via `Nat.le_total`, and
/// normalizing the resulting bound into `CReal.Cauchy`'s own
/// `natDivSucc K m + natDivSucc K n` shape, are left to whichever piece
/// assembles `sumRange_cauchy_of_dominated` itself.
fn declare_sum_range_cauchy_dominated_ordered(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_add = d.prelude().add;
    let nat_le_dest = d.prelude().le_dest;
    let rat = p.rat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let pointwise_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fx = d.apply(f, &[x]);
        let gx = d.apply(g, &[x]);
        let abs_fx = cabs(d, p, fx);
        let leq = cle(d, p, abs_fx, gx);
        d.pi_fv(x_fv, nat, leq)
    };
    let hyp1_fv = d.fresh_fvar();
    let hyp1 = d.kernel().fvar(hyp1_fv);

    let cauchy_hyp_ty = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);
        let sum_pp = d.const_app(p.sum_range, &[g, pp]);
        let sum_qq = d.const_app(p.sum_range, &[g, qq]);
        let left = sample(d, p, sum_pp, pp);
        let right = sample(d, p, sum_qq, qq);
        let diff = rsub(d, rat, left, right);
        let bpp = div_succ_var(d, p, k, pp);
        let bqq = div_succ_var(d, p, k, qq);
        let bound = radd(d, bpp, bqq);
        let claim = within(d, p, diff, bound);
        let over_qq = d.pi_fv(qq_fv, nat, claim);
        d.pi_fv(pp_fv, nat, over_qq)
    };
    let hyp2_fv = d.fresh_fvar();
    let hyp2 = d.kernel().fvar(hyp2_fv);

    let hle_ty = d.le(a, b);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let sum_f_a = d.const_app(p.sum_range, &[f, a]);

    let target_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sum_f_x = d.const_app(p.sum_range, &[f, x]);
        let y = sample(d, p, sum_f_x, x);
        let z = sample(d, p, sum_f_a, a);
        let diff = rsub(d, rat, y, z);
        let bound = dominated_canonical_bound(d, p, k, a, x);
        within(d, p, diff, bound)
    };
    let target = target_at(d, b);

    // pred := λ n, Eq Nat (add a n) b.
    let pred = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sum = d.const_app(nat_add, &[a, n]);
        let body = d.eq(sum, b);
        d.lam_fv(n_fv, nat, body)
    };

    let represented = d.const_app(nat_le_dest, &[a, b, hle]);

    let minor = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let a_plus_n = d.const_app(nat_add, &[a, n]);
        let e_ty = d.eq(a_plus_n, b);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        // body_at_an : target_at(add a n) -- exactly
        // `dominated_canonical_at f g k a n hyp1 hyp2`'s own conclusion.
        let body_at_an = dominated_canonical_at(d, p, f, g, k, a, n, hyp1, hyp2);
        let rewritten = nat_rewrite_prop(d, a_plus_n, b, e, body_at_an, &|d, x| target_at(d, x));

        let with_e = d.lam_fv(e_fv, e_ty, rewritten);
        d.lam_fv(n_fv, nat, with_e)
    };

    let proof_body = exists_elim(d, pred, target, represented, minor);

    let ty = {
        let after_hle = d.arrow(hle_ty, target);
        let after_hyp2 = d.arrow(cauchy_hyp_ty, after_hle);
        let after_hyp1 = d.arrow(pointwise_ty, after_hyp2);
        let over_b = d.pi_fv(b_fv, nat, after_hyp1);
        let over_a = d.pi_fv(a_fv, nat, over_b);
        let over_k = d.pi_fv(k_fv, nat, over_a);
        let over_g = d.pi_fv(g_fv, fn_ty, over_k);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, proof_body);
        let with_hyp2 = d.lam_fv(hyp2_fv, cauchy_hyp_ty, with_hle);
        let with_hyp1 = d.lam_fv(hyp1_fv, pointwise_ty, with_hyp2);
        let over_b = d.lam_fv(b_fv, nat, with_hyp1);
        let over_a = d.lam_fv(a_fv, nat, over_b);
        let over_k = d.lam_fv(k_fv, nat, over_a);
        let over_g = d.lam_fv(g_fv, fn_ty, over_k);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_cauchy_dominated_ordered,
        uparams: vec![],
        ty,
        value,
    })
}

// --- bound normalization for `sumRange_cauchy_dominated_ordered` -----------

/// `Rat.add_assoc a b c : Eq ((a+b)+c) (a+(b+c))`, applied directly.
fn assoc_fwd_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    d.lemma(p.rat.add_assoc, &[a, b, c])
}

/// `Eq (a+(b+c)) ((a+b)+c)` — [`assoc_fwd_eq`] read backwards via `rsymm`.
pub(super) fn assoc_rev_eq(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let ab = radd(d, a, b);
    let lhs = radd(d, ab, c);
    let bc = radd(d, b, c);
    let rhs = radd(d, a, bc);
    let fwd = assoc_fwd_eq(d, p, a, b, c);
    rsymm(d, lhs, rhs, fwd)
}

/// `Eq (natDivSucc a j + natDivSucc b j) (natDivSucc (a+b) j)`, via
/// `Rat.natDivSucc_add` — the one fusion move
/// [`declare_sum_range_cauchy_dominated_ordered_normalized`]'s bound
/// normalization runs repeatedly, at whichever pair of same-index leaves its
/// current reassociation has just brought adjacent. Returns `(fused,
/// eq_proof)`.
pub(super) fn fuse_same_index(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a_num: ExprId,
    b_num: ExprId,
    idx: ExprId,
) -> (ExprId, ExprId) {
    let eq = d.lemma(p.rat.nat_div_succ_add, &[a_num, b_num, idx]);
    let sum_num = d.add(a_num, b_num);
    let fused = div_succ_var(d, p, sum_num, idx);
    (fused, eq)
}

/// `CReal.sumRange_cauchy_dominated_ordered_normalized` — bound
/// normalization, `series.rs`'s module documentation's second remaining gap
/// toward `sumRange_cauchy_of_dominated`. Post-processes
/// [`declare_sum_range_cauchy_dominated_ordered`]'s own eleven-`natDivSucc`-leaf
/// bound into a single `Cauchy`-shaped `natDivSucc K' b + natDivSucc K' a`,
/// `K' := k+8` (as a nested `Nat.add`-by-literal chain, never simplified to
/// the literal `8` — see the module documentation for why that keeps every
/// join here pure `Nat` defeq rather than needing `Nat.add_assoc`/
/// `Nat.add_comm`). The `b`-side reaches `K'` exactly, with no padding; the
/// `a`-side (`k+2`) is padded up to `K'` by one `Rat.natDivSucc_le_add_left`
/// (`e := 6`), accepted by the kernel purely because `(k+2)+6` and `k+8`
/// reduce to the same `Nat.succ` tower.
///
/// Rebuilds `dominated_canonical_bound k a b` leaf-by-leaf (`m := a`,
/// `x := b`, exactly [`dominated_canonical_legs`]'s own construction,
/// duplicated rather than reused so every sub-piece — the four
/// `1/(shift b+1)` legs to widen, the seven other leaves to fuse — is in
/// scope), widens the shifted legs via `half_shift_le`, then fuses the
/// result down to two terms across two passes: the inner three-term cluster
/// (`sum_range_tail_cauchy_within`'s own bound shape) fuses to `bxkb + dkm`
/// first, then the outer combination (reusing that result) fuses to
/// `finalX + mkm2`. Neither pass is symmetric in `a`/`b` — the shifted index
/// only ever attaches to `b` — so this remains the **ordered-pair** theorem
/// (`a ≤ b` required) with the Cauchy hypothesis still in its raw witnessed
/// form; the `Nat.le_total` case split and the `CReal.Cauchy` existential
/// itself are left to whichever piece assembles `sumRange_cauchy_of_dominated`
/// next.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sum_range_cauchy_dominated_ordered_normalized(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let rat = p.rat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let pointwise_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fx = d.apply(f, &[x]);
        let gx = d.apply(g, &[x]);
        let abs_fx = cabs(d, p, fx);
        let leq = cle(d, p, abs_fx, gx);
        d.pi_fv(x_fv, nat, leq)
    };
    let hyp1_fv = d.fresh_fvar();
    let hyp1 = d.kernel().fvar(hyp1_fv);

    let cauchy_hyp_ty = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);
        let sum_pp = d.const_app(p.sum_range, &[g, pp]);
        let sum_qq = d.const_app(p.sum_range, &[g, qq]);
        let left = sample(d, p, sum_pp, pp);
        let right = sample(d, p, sum_qq, qq);
        let diff = rsub(d, rat, left, right);
        let bpp = div_succ_var(d, p, k, pp);
        let bqq = div_succ_var(d, p, k, qq);
        let bound = radd(d, bpp, bqq);
        let claim = within(d, p, diff, bound);
        let over_qq = d.pi_fv(qq_fv, nat, claim);
        d.pi_fv(pp_fv, nat, over_qq)
    };
    let hyp2_fv = d.fresh_fvar();
    let hyp2 = d.kernel().fvar(hyp2_fv);

    let hle_ty = d.le(a, b);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    // raw : Within (seq (sumRange f b) b - seq (sumRange f a) a)
    //              (dominated_canonical_bound k a b)
    let raw = d.lemma(
        p.sum_range_cauchy_dominated_ordered,
        &[f, g, k, a, b, hyp1, hyp2, hle],
    );

    let sum_f_b = d.const_app(p.sum_range, &[f, b]);
    let sum_f_a = d.const_app(p.sum_range, &[f, a]);
    let y = sample(d, p, sum_f_b, b);
    let z = sample(d, p, sum_f_a, a);
    let diff = rsub(d, rat, y, z);

    // Rebuild `dominated_canonical_bound k a b` leaf-by-leaf, matching
    // `dominated_canonical_legs`'s own construction exactly (`m := a`,
    // `x := b`), so every sub-piece needed below is in scope.
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let six_nat = d.num(6);

    let t = shift(d, b);
    let leaf_a = div_succ(d, p, 1, t); // natDivSucc(1, shift b)
    let leaf_b = div_succ(d, p, 1, b); // natDivSucc(1, b)
    let leaf_c = div_succ_var(d, p, k, b); // natDivSucc(k, b)
    let leaf_d = div_succ_var(d, p, k, a); // natDivSucc(k, a)
    let leaf_e = div_succ(d, p, 1, a); // natDivSucc(1, a)
    let leaf_f = div_succ(d, p, 2, b); // natDivSucc(2, b)

    let bxy = radd(d, leaf_a, leaf_b);
    let b2 = radd(d, leaf_c, leaf_d);
    let bzw = radd(d, leaf_e, leaf_a);
    let bxy_b2 = radd(d, bxy, b2);
    let total_bound_g = radd(d, bxy_b2, bzw);
    let byz = radd(d, total_bound_g, leaf_f);
    let bxy_byz = radd(d, bxy, byz);
    let total = radd(d, bxy_byz, bzw);

    // --- widen: every `natDivSucc(1, shift b)` leaf up to `natDivSucc(1, b)`.
    let half = half_shift_le(d, p, b); // le(leaf_a, leaf_b)
    let refl_leaf_b = d.lemma(rat.le_refl, &[leaf_b]);
    let refl_leaf_e = d.lemma(rat.le_refl, &[leaf_e]);
    let refl_b2 = d.lemma(rat.le_refl, &[b2]);
    let refl_leaf_f = d.lemma(rat.le_refl, &[leaf_f]);

    let bb = radd(d, leaf_b, leaf_b);
    let bxy_le = d.lemma(
        rat.add_le_add,
        &[leaf_a, leaf_b, leaf_b, leaf_b, half, refl_leaf_b],
    ); // le(bxy, bb)

    let eb = radd(d, leaf_e, leaf_b);
    let bzw_le = d.lemma(
        rat.add_le_add,
        &[leaf_e, leaf_e, leaf_a, leaf_b, refl_leaf_e, half],
    ); // le(bzw, eb)

    let bb_b2 = radd(d, bb, b2);
    let tbg_wide = radd(d, bb_b2, eb);
    let tbg_le = {
        let step = d.lemma(rat.add_le_add, &[bxy, bb, b2, b2, bxy_le, refl_b2]);
        d.lemma(rat.add_le_add, &[bxy_b2, bb_b2, bzw, eb, step, bzw_le])
    }; // le(total_bound_g, tbg_wide)

    let byz_wide = radd(d, tbg_wide, leaf_f);
    let byz_le = d.lemma(
        rat.add_le_add,
        &[total_bound_g, tbg_wide, leaf_f, leaf_f, tbg_le, refl_leaf_f],
    ); // le(byz, byz_wide)

    let bb_byzwide = radd(d, bb, byz_wide);
    let total_wide = radd(d, bb_byzwide, eb);
    let total_le = {
        let step = d.lemma(rat.add_le_add, &[bxy, bb, byz, byz_wide, bxy_le, byz_le]);
        d.lemma(
            rat.add_le_add,
            &[bxy_byz, bb_byzwide, bzw, eb, step, bzw_le],
        )
    }; // le(total, total_wide)

    // --- fuse pass 1: `tbg_wide = (bb + (leaf_c+leaf_d)) + eb` into
    // `bxkb + dkm` — a single natDivSucc leaf per side.
    let s0 = tbg_wide;
    let (bx2, fuse_bb) = fuse_same_index(d, p, one_nat, one_nat, b); // eq(bb, bx2)
    let bx2_num = d.add(one_nat, one_nat);
    let bx2_b2 = radd(d, bx2, b2);
    let s1 = radd(d, bx2_b2, eb);
    let step1 = rcongr(d, bb, bx2, fuse_bb, &|d, t| {
        let t_b2 = radd(d, t, b2);
        radd(d, t_b2, eb)
    });

    let rev2 = assoc_rev_eq(d, p, bx2, leaf_c, leaf_d); // eq(bx2+(c+d), (bx2+c)+d)
    let bx2_c = radd(d, bx2, leaf_c);
    let bx2_c_d = radd(d, bx2_c, leaf_d);
    let s2a = radd(d, bx2_c_d, eb);
    let step2a = rcongr(d, bx2_b2, bx2_c_d, rev2, &|d, t| radd(d, t, eb));

    // `Nat.add` recurses on its RIGHT argument, so a `k`-containing numerator
    // must never sit there (`Add(bx2_num, k)` is stuck; `Add(k, bx2_num)`
    // reduces). This `comm2b` swap keeps that invariant for every fuse below.
    let comm2b = d.lemma(rat.add_comm, &[bx2, leaf_c]); // eq(bx2+c, c+bx2)
    let c_bx2 = radd(d, leaf_c, bx2);
    let c_bx2_d = radd(d, c_bx2, leaf_d);
    let s2 = radd(d, c_bx2_d, eb);
    let step2b = rcongr(d, bx2_c, c_bx2, comm2b, &|d, t| {
        let t_d = radd(d, t, leaf_d);
        radd(d, t_d, eb)
    });

    let (bxk, fuse_bxk) = fuse_same_index(d, p, k, bx2_num, b); // eq(c+bx2, bxk)
    let bxk_num = d.add(k, bx2_num); // k on the left: reduces cleanly
    let bxk_d = radd(d, bxk, leaf_d);
    let s3 = radd(d, bxk_d, eb);
    let step3 = rcongr(d, c_bx2, bxk, fuse_bxk, &|d, t| {
        let t_d = radd(d, t, leaf_d);
        radd(d, t_d, eb)
    });

    let step4 = assoc_fwd_eq(d, p, bxk, leaf_d, eb); // eq((bxk+d)+eb, bxk+(d+eb))
    let d_eb = radd(d, leaf_d, eb);
    let s4 = radd(d, bxk, d_eb);

    let rev5 = assoc_rev_eq(d, p, leaf_d, leaf_e, leaf_b); // eq(d+(e+b), (d+e)+b)
    let d_e = radd(d, leaf_d, leaf_e);
    let de_b = radd(d, d_e, leaf_b);
    let s5 = radd(d, bxk, de_b);
    let step5 = rcongr(d, d_eb, de_b, rev5, &|d, t| radd(d, bxk, t));

    let (dkm, fuse_dkm) = fuse_same_index(d, p, k, one_nat, a); // eq(d+e, dkm)
    let dkm_num = d.add(k, one_nat);
    let dkm_b = radd(d, dkm, leaf_b);
    let s6 = radd(d, bxk, dkm_b);
    let step6 = rcongr(d, d_e, dkm, fuse_dkm, &|d, t| {
        let t_b = radd(d, t, leaf_b);
        radd(d, bxk, t_b)
    });

    let comm7 = d.lemma(rat.add_comm, &[dkm, leaf_b]); // eq(dkm+b, b+dkm)
    let b_dkm = radd(d, leaf_b, dkm);
    let s7 = radd(d, bxk, b_dkm);
    let step7 = rcongr(d, dkm_b, b_dkm, comm7, &|d, t| radd(d, bxk, t));

    let step8 = assoc_rev_eq(d, p, bxk, leaf_b, dkm); // eq(bxk+(b+dkm), (bxk+b)+dkm)
    let bxk_b = radd(d, bxk, leaf_b);
    let s8 = radd(d, bxk_b, dkm);

    let (bxkb, fuse_bxkb) = fuse_same_index(d, p, bxk_num, one_nat, b); // eq(bxk+b, bxkb)
    let bxkb_num = d.add(bxk_num, one_nat);
    let s9 = radd(d, bxkb, dkm);
    let step9 = rcongr(d, bxk_b, bxkb, fuse_bxkb, &|d, t| radd(d, t, dkm));

    let (_, tbg_final_eq) = rchain(
        d,
        s0,
        &[
            (s1, step1),
            (s2a, step2a),
            (s2, step2b),
            (s3, step3),
            (s4, step4),
            (s5, step5),
            (s6, step6),
            (s7, step7),
            (s8, step8),
            (s9, step9),
        ],
    ); // eq(tbg_wide, s9 = bxkb + dkm)

    // --- fuse pass 2: `total_wide = (bb + (tbg_wide+leaf_f)) + eb`, through
    // pass 1's result, into `finalX + mkm2`.
    let u0 = total_wide;
    let byz_wide2 = radd(d, s9, leaf_f);
    let byz_eq = rcongr(d, tbg_wide, s9, tbg_final_eq, &|d, t| radd(d, t, leaf_f));
    let bb_byzwide2 = radd(d, bb, byz_wide2);
    let u1 = radd(d, bb_byzwide2, eb);
    let stepa = rcongr(d, byz_wide, byz_wide2, byz_eq, &|d, t| {
        let bb_t = radd(d, bb, t);
        radd(d, bb_t, eb)
    });

    let bx2_byzwide2 = radd(d, bx2, byz_wide2);
    let u2 = radd(d, bx2_byzwide2, eb);
    let stepb = rcongr(d, bb, bx2, fuse_bb, &|d, t| {
        let t_byzwide2 = radd(d, t, byz_wide2);
        radd(d, t_byzwide2, eb)
    });

    // (bxkb+dkm)+f ~ (bxkb+f)+dkm
    let bxkb_f = radd(d, bxkb, leaf_f);
    let byz_wide3 = radd(d, bxkb_f, dkm);
    let byz_wide2_eq3 = {
        let c1 = assoc_fwd_eq(d, p, bxkb, dkm, leaf_f); // eq((bxkb+dkm)+f, bxkb+(dkm+f))
        let dkm_f = radd(d, dkm, leaf_f);
        let mid1 = radd(d, bxkb, dkm_f);
        let comm_c2 = d.lemma(rat.add_comm, &[dkm, leaf_f]); // eq(dkm+f, f+dkm)
        let f_dkm = radd(d, leaf_f, dkm);
        let mid2 = radd(d, bxkb, f_dkm);
        let step_c2 = rcongr(d, dkm_f, f_dkm, comm_c2, &|d, t| radd(d, bxkb, t));
        let step_c3 = assoc_rev_eq(d, p, bxkb, leaf_f, dkm); // eq(bxkb+(f+dkm), (bxkb+f)+dkm)
        let (_, chained) = rchain(
            d,
            byz_wide2,
            &[(mid1, c1), (mid2, step_c2), (byz_wide3, step_c3)],
        );
        chained
    };
    let bx2_byzwide3 = radd(d, bx2, byz_wide3);
    let u3 = radd(d, bx2_byzwide3, eb);
    let stepc = rcongr(d, byz_wide2, byz_wide3, byz_wide2_eq3, &|d, t| {
        let bx2_t = radd(d, bx2, t);
        radd(d, bx2_t, eb)
    });

    // eq(bx2+(bxkb_f+dkm), (bx2+bxkb_f)+dkm) — note bxkb_f+dkm is `byz_wide3`
    // itself, so this is exactly the inner part of `u3` before its `+eb`.
    let raw_stepd = assoc_rev_eq(d, p, bx2, bxkb_f, dkm);
    let bx2_bxkbf = radd(d, bx2, bxkb_f);
    let bx2_bxkbf_dkm = radd(d, bx2_bxkbf, dkm);
    let stepd = rcongr(d, bx2_byzwide3, bx2_bxkbf_dkm, raw_stepd, &|d, t| {
        radd(d, t, eb)
    });
    let u4 = radd(d, bx2_bxkbf_dkm, eb);

    let step_e_inner = assoc_rev_eq(d, p, bx2, bxkb, leaf_f); // eq(bx2+(bxkb+f), (bx2+bxkb)+f)
    let bx2_bxkb = radd(d, bx2, bxkb);
    let bx2bxkb_f = radd(d, bx2_bxkb, leaf_f);
    let bx2bxkbf_dkm = radd(d, bx2bxkb_f, dkm);
    let u5 = radd(d, bx2bxkbf_dkm, eb);
    let stepe = rcongr(d, bx2_bxkbf, bx2bxkb_f, step_e_inner, &|d, t| {
        let t_dkm = radd(d, t, dkm);
        radd(d, t_dkm, eb)
    });

    // Same invariant as pass 1's `comm2b`: `bxkb_num` contains `k`, so it must
    // sit on the LEFT of the fuse below, never the right.
    let comm_f0 = d.lemma(rat.add_comm, &[bx2, bxkb]); // eq(bx2+bxkb, bxkb+bx2)
    let bxkb_bx2 = radd(d, bxkb, bx2);
    let bxkbbx2_f = radd(d, bxkb_bx2, leaf_f);
    let bxkbbx2f_dkm = radd(d, bxkbbx2_f, dkm);
    let u5b = radd(d, bxkbbx2f_dkm, eb);
    let stepe2 = rcongr(d, bx2_bxkb, bxkb_bx2, comm_f0, &|d, t| {
        let t_f = radd(d, t, leaf_f);
        let tf_dkm = radd(d, t_f, dkm);
        radd(d, tf_dkm, eb)
    });

    let (bxk2, fuse_bxk2) = fuse_same_index(d, p, bxkb_num, bx2_num, b); // eq(bxkb+bx2, bxk2)
    let bxk2_num = d.add(bxkb_num, bx2_num); // k on the left: reduces cleanly
    let bxk2_f = radd(d, bxk2, leaf_f);
    let bxk2f_dkm = radd(d, bxk2_f, dkm);
    let u6 = radd(d, bxk2f_dkm, eb);
    let stepf = rcongr(d, bxkb_bx2, bxk2, fuse_bxk2, &|d, t| {
        let t_f = radd(d, t, leaf_f);
        let tf_dkm = radd(d, t_f, dkm);
        radd(d, tf_dkm, eb)
    });

    let (bxk3, fuse_bxk3) = fuse_same_index(d, p, bxk2_num, two_nat, b); // eq(bxk2+f, bxk3)
    let bxk3_num = d.add(bxk2_num, two_nat);
    let bxk3_dkm = radd(d, bxk3, dkm);
    let u7 = radd(d, bxk3_dkm, eb);
    let stepg = rcongr(d, bxk2_f, bxk3, fuse_bxk3, &|d, t| {
        let t_dkm = radd(d, t, dkm);
        radd(d, t_dkm, eb)
    });

    let steph = assoc_fwd_eq(d, p, bxk3, dkm, eb); // eq((bxk3+dkm)+eb, bxk3+(dkm+eb))
    let dkm_eb = radd(d, dkm, eb);
    let u8 = radd(d, bxk3, dkm_eb);

    let rev_i = assoc_rev_eq(d, p, dkm, leaf_e, leaf_b); // eq(dkm+(e+b), (dkm+e)+b)
    let dkm_e = radd(d, dkm, leaf_e);
    let dkme_b = radd(d, dkm_e, leaf_b);
    let u9 = radd(d, bxk3, dkme_b);
    let stepi = rcongr(d, dkm_eb, dkme_b, rev_i, &|d, t| radd(d, bxk3, t));

    let (mkm2, fuse_mkm2) = fuse_same_index(d, p, dkm_num, one_nat, a); // eq(dkm+e, mkm2)
    let mkm2_num = d.add(dkm_num, one_nat);
    let mkm2_b = radd(d, mkm2, leaf_b);
    let u10 = radd(d, bxk3, mkm2_b);
    let stepj = rcongr(d, dkm_e, mkm2, fuse_mkm2, &|d, t| {
        let t_b = radd(d, t, leaf_b);
        radd(d, bxk3, t_b)
    });

    let comm_k = d.lemma(rat.add_comm, &[mkm2, leaf_b]); // eq(mkm2+b, b+mkm2)
    let b_mkm2 = radd(d, leaf_b, mkm2);
    let u11 = radd(d, bxk3, b_mkm2);
    let stepk = rcongr(d, mkm2_b, b_mkm2, comm_k, &|d, t| radd(d, bxk3, t));

    let stepl = assoc_rev_eq(d, p, bxk3, leaf_b, mkm2); // eq(bxk3+(b+mkm2), (bxk3+b)+mkm2)
    let bxk3_b = radd(d, bxk3, leaf_b);
    let u12 = radd(d, bxk3_b, mkm2);

    let (finalx, fuse_finalx) = fuse_same_index(d, p, bxk3_num, one_nat, b); // eq(bxk3+b, finalx)
    let u13 = radd(d, finalx, mkm2);
    let stepm = rcongr(d, bxk3_b, finalx, fuse_finalx, &|d, t| radd(d, t, mkm2));

    let (_, total_wide_eq) = rchain(
        d,
        u0,
        &[
            (u1, stepa),
            (u2, stepb),
            (u3, stepc),
            (u4, stepd),
            (u5, stepe),
            (u5b, stepe2),
            (u6, stepf),
            (u7, stepg),
            (u8, steph),
            (u9, stepi),
            (u10, stepj),
            (u11, stepk),
            (u12, stepl),
            (u13, stepm),
        ],
    ); // eq(total_wide, u13 = finalx + mkm2)

    let total_le_u13 = rat_eq_rewrite(d, total_wide, u13, total_wide_eq, total_le, &|d, t| {
        rle(d, rat, total, t)
    }); // le(total, finalx + mkm2)

    // --- pad `mkm2`'s numerator (k+2) up to `finalx`'s own (k+8): pure
    // `Nat` defeq, no `Rat`-level rewrite needed for the alignment itself.
    let k_prime = d.add(bxk3_num, one_nat); // = k+8, defeq to finalx's own numerator
    let refl_finalx = d.lemma(rat.le_refl, &[finalx]);
    let km_side = div_succ_var(d, p, k_prime, a); // natDivSucc(K', a)
    let padding = d.lemma(rat.nat_div_succ_le_add_left, &[mkm2_num, six_nat, a]);
    // le(mkm2, natDivSucc(mkm2_num+6, a)) — defeq to le(mkm2, km_side)

    let target_bound = radd(d, finalx, km_side); // natDivSucc(K', b) + natDivSucc(K', a)
    let final_order = d.lemma(
        rat.add_le_add,
        &[finalx, finalx, mkm2, km_side, refl_finalx, padding],
    ); // le(finalx + mkm2, target_bound)

    let final_le = d.lemma(
        rat.le_trans,
        &[total, u13, target_bound, total_le_u13, final_order],
    ); // le(total, target_bound)

    let normalized = weaken(d, p, diff, total, target_bound, raw, final_le);

    let ty = {
        let claim = within(d, p, diff, target_bound);
        let after_hle = d.arrow(hle_ty, claim);
        let after_hyp2 = d.arrow(cauchy_hyp_ty, after_hle);
        let after_hyp1 = d.arrow(pointwise_ty, after_hyp2);
        let over_b = d.pi_fv(b_fv, nat, after_hyp1);
        let over_a = d.pi_fv(a_fv, nat, over_b);
        let over_k = d.pi_fv(k_fv, nat, over_a);
        let over_g = d.pi_fv(g_fv, fn_ty, over_k);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, normalized);
        let with_hyp2 = d.lam_fv(hyp2_fv, cauchy_hyp_ty, with_hle);
        let with_hyp1 = d.lam_fv(hyp1_fv, pointwise_ty, with_hyp2);
        let over_b = d.lam_fv(b_fv, nat, with_hyp1);
        let over_a = d.lam_fv(a_fv, nat, over_b);
        let over_k = d.lam_fv(k_fv, nat, over_a);
        let over_g = d.lam_fv(g_fv, fn_ty, over_k);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_cauchy_dominated_ordered_normalized,
        uparams: vec![],
        ty,
        value,
    })
}

/// `∀ pp qq, Within (seq (h pp) pp − seq (h qq) qq) (natDivSucc k pp +
/// natDivSucc k qq)` — `CReal.Cauchy h`'s own body at a (possibly symbolic)
/// numerator `k`, reconstructed call-for-call from `sample`/`rsub`/
/// `div_succ_var`/`radd`/`within`/`pi_fv` (exactly `convergence.rs`'s private
/// `cauchy_body`'s own construction; not reused — `convergence.rs` is out of
/// scope for this slice) so it is syntactically the predicate `CReal.Cauchy`
/// itself unfolds to, and a witness/proof built against it type-checks
/// directly against `Cauchy h` with no explicit rewrite.
pub(super) fn sum_range_cauchy_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    h: ExprId,
    k: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hm = d.apply(h, &[m]);
    let hn = d.apply(h, &[n]);
    let left = sample(d, p, hm, m);
    let right = sample(d, p, hn, n);
    let diff = rsub(d, rat, left, right);
    let bm = div_succ_var(d, p, k, m);
    let bn = div_succ_var(d, p, k, n);
    let bound = radd(d, bm, bn);
    let claim = within(d, p, diff, bound);
    let over_n = d.pi_fv(n_fv, nat, claim);
    d.pi_fv(m_fv, nat, over_n)
}

/// `CReal.sumRange_cauchy_of_dominated : ∀ f g, (∀ k, le (abs (f k)) (g k))
/// → Cauchy (sumRange g) → Cauchy (sumRange f)` — the piece `series.rs`'s
/// module documentation names as the goal: eliminate the `Cauchy (sumRange
/// g)` existential (`Exists.rec`, elem type `Nat`,
/// [`declare_sum_range_cauchy_dominated_ordered`]'s own `exists_elim` idiom
/// against a different existential), split `∀ m n` on the **decidable**
/// `Nat.le_total` (never branch on the *undecidable* [`super::CRealPrelude::le`]
/// over `CReal` itself — the whole reason this step is tractable), and in
/// each branch instantiate
/// [`declare_sum_range_cauchy_dominated_ordered_normalized`] at whichever of
/// `(m, n)`/`(n, m)` satisfies its own `a ≤ b` side condition:
///
/// - `n ≤ m`: calling the theorem at `(a, b) := (n, m)` lands **exactly** on
///   `Cauchy`'s own `(m, n)` sample and `radd` order — no further rewrite.
/// - `m ≤ n`: calling it at `(a, b) := (m, n)` gives `Within (seq (f n) n −
///   seq (f m) m)` in the `(n, m)`-ordered bound; reaching `Cauchy`'s
///   `(m, n)`-ordered shape needs one [`within_symm`] flip (the difference)
///   plus one `Rat.add_comm` (the bound), since this theorem's bound is not
///   symmetric in its two arguments.
///
/// Both branches use the **same** `K' := k+8` (built once, outside the case
/// split, as eight nested `Nat.succ`s of the Cauchy witness `k` rather than
/// the source theorem's own nested-`Nat.add`-by-literal chain — both reduce
/// to the identical `succ` tower, but a bare `succ` chain sidesteps the
/// "symbolic side left of `Nat.add`" trap entirely), so
/// [`CRealPrelude::sum_range_cauchy_dominated_ordered_normalized`]'s bound in
/// each branch is defeq to the one `Exists.intro` closes over.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_sum_range_cauchy_of_dominated(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let rat = p.rat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);

    let pointwise_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fx = d.apply(f, &[x]);
        let gx = d.apply(g, &[x]);
        let abs_fx = cabs(d, p, fx);
        let leq = cle(d, p, abs_fx, gx);
        d.pi_fv(x_fv, nat, leq)
    };
    let hyp1_fv = d.fresh_fvar();
    let hyp1 = d.kernel().fvar(hyp1_fv);

    let sum_g = d.const_app(p.sum_range, &[g]);
    let cauchy_g_ty = d.const_app(p.cauchy, &[sum_g]);
    let hyp2_fv = d.fresh_fvar();
    let hyp2 = d.kernel().fvar(hyp2_fv);

    let sum_f = d.const_app(p.sum_range, &[f]);
    let target = d.const_app(p.cauchy, &[sum_f]);

    // predicate_g := λ k, sum_range_cauchy_body(sum_g, k) — syntactically
    // `Cauchy (sumRange g)`'s own unfolded predicate.
    let predicate_g = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = sum_range_cauchy_body(d, p, sum_g, k);
        d.lam_fv(k_fv, nat, body)
    };

    // minor : ∀ k, predicate_g k → target.
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hyp2_body_ty = sum_range_cauchy_body(d, p, sum_g, k);
        let hyp2_body_fv = d.fresh_fvar();
        let hyp2_body = d.kernel().fvar(hyp2_body_fv);

        // K' := k+8, eight bare `Nat.succ`s — already fully reduced, so no
        // `Nat.add` operand-order trap to fall into.
        let mut k_prime = k;
        for _ in 0..8 {
            k_prime = d.succ(k_prime);
        }

        // case_proof : ∀ m n, Within (seq (sumRange f m) m − seq (sumRange f
        // n) n) (natDivSucc k_prime m + natDivSucc k_prime n).
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
            let bm = div_succ_var(d, p, k_prime, m);
            let bn = div_succ_var(d, p, k_prime, n);
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
                // m ≤ n: ordered_normalized(a := m, b := n) gives
                // Within (seq f n n − seq f m m) (bn + bm); flip the
                // difference, then reorder the bound.
                &|d, hmn| {
                    let raw = d.lemma(
                        p.sum_range_cauchy_dominated_ordered_normalized,
                        &[f, g, k, m, n, hyp1, hyp2_body, hmn],
                    );
                    let bound_nm = radd(d, bn, bm);
                    let flipped = within_symm(d, p, z_n, y_m, bound_nm, raw);
                    let comm_eq = d.lemma(p.rat.add_comm, &[bn, bm]);
                    rat_eq_rewrite(d, bound_nm, bound_mn, comm_eq, flipped, &|d, t| {
                        within(d, p, diff_mn, t)
                    })
                },
                // n ≤ m: ordered_normalized(a := n, b := m) gives exactly
                // Within (seq f m m − seq f n n) (bm + bn) — no rewrite.
                &|d, hnm| {
                    d.lemma(
                        p.sum_range_cauchy_dominated_ordered_normalized,
                        &[f, g, k, n, m, hyp1, hyp2_body, hnm],
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
        let target_proof = exists_nat_intro(d, p, predicate_f, k_prime, case_proof);

        let with_hyp2_body = d.lam_fv(hyp2_body_fv, hyp2_body_ty, target_proof);
        d.lam_fv(k_fv, nat, with_hyp2_body)
    };

    let proof_body = exists_elim(d, predicate_g, target, hyp2, minor);

    let ty = {
        let after_hyp2 = d.arrow(cauchy_g_ty, target);
        let after_hyp1 = d.arrow(pointwise_ty, after_hyp2);
        let over_g = d.pi_fv(g_fv, fn_ty, after_hyp1);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_hyp2 = d.lam_fv(hyp2_fv, cauchy_g_ty, proof_body);
        let with_hyp1 = d.lam_fv(hyp1_fv, pointwise_ty, with_hyp2);
        let over_g = d.lam_fv(g_fv, fn_ty, with_hyp1);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_cauchy_of_dominated,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_converges_of_dominated : ∀ f g, (∀ k, le (abs (f k)) (g
/// k)) → Cauchy (sumRange g) → Exists (fun L => Converges (sumRange f) L)`.
///
/// The composition the module documentation named as the remaining step,
/// once [`CRealPrelude::converges_of_cauchy`] closed the `Cauchy →
/// Converges` bridge (`creal/convergence.rs`): apply
/// [`CRealPrelude::sum_range_cauchy_of_dominated`] to the two hypotheses to
/// get `Cauchy (sumRange f)`, then `converges_of_cauchy` directly. Neither
/// step introduces or eliminates an existential here — both are
/// already-declared theorems, applied in sequence; only the **target type**
/// (`Exists CReal (fun L => Converges (sumRange f) L)`) has to be built by
/// hand, via [`exists_ty`]/[`converges_applied`] (`convergence.rs`, bumped to
/// `pub(super)` for exactly this reuse).
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_sum_range_converges_of_dominated(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);

    let pointwise_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fx = d.apply(f, &[x]);
        let gx = d.apply(g, &[x]);
        let abs_fx = cabs(d, p, fx);
        let leq = cle(d, p, abs_fx, gx);
        d.pi_fv(x_fv, nat, leq)
    };
    let hyp1_fv = d.fresh_fvar();
    let hyp1 = d.kernel().fvar(hyp1_fv);

    let sum_g = d.const_app(p.sum_range, &[g]);
    let cauchy_g_ty = d.const_app(p.cauchy, &[sum_g]);
    let hyp2_fv = d.fresh_fvar();
    let hyp2 = d.kernel().fvar(hyp2_fv);

    let sum_f = d.const_app(p.sum_range, &[f]);

    // cauchy_f : Cauchy (sumRange f).
    let cauchy_f = d.lemma(p.sum_range_cauchy_of_dominated, &[f, g, hyp1, hyp2]);
    // proof_body : Exists CReal (fun L => Converges (sumRange f) L).
    let proof_body = d.lemma(p.converges_of_cauchy, &[sum_f, cauchy_f]);

    let pred_f = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let conv_l = converges_applied(d, p, sum_f, l);
        d.lam_fv(l_fv, carrier, conv_l)
    };
    let target = exists_ty(d, p, carrier, pred_f);

    let ty = {
        let after_hyp2 = d.arrow(cauchy_g_ty, target);
        let after_hyp1 = d.arrow(pointwise_ty, after_hyp2);
        let over_g = d.pi_fv(g_fv, fn_ty, after_hyp1);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_hyp2 = d.lam_fv(hyp2_fv, cauchy_g_ty, proof_body);
        let with_hyp1 = d.lam_fv(hyp1_fv, pointwise_ty, with_hyp2);
        let over_g = d.lam_fv(g_fv, fn_ty, with_hyp1);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_converges_of_dominated,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.sumRange_comparisonTest : ∀ a b, (∀ k, le zero (a k)) → (∀ k, le
/// (a k) (b k)) → Exists (fun M => Converges (sumRange b) M) → Exists (fun L
/// => Converges (sumRange a) L)` — the comparison test as usually stated.
///
/// Converts the `Exists … Converges (sumRange b) M` hypothesis to `Cauchy
/// (sumRange b)` via [`creal_exists_elim`] (`convergence.rs`'s `exists_elim`,
/// reused over `elem_ty := CReal`) eliminating into
/// [`CRealPrelude::converges_cauchy`] applied at the witness — a target
/// (`Cauchy (sumRange b)`) that does not mention the eliminated witness `M`,
/// exactly the shape [`declare_sum_range_cauchy_of_dominated`] already uses
/// against a *different* existential over `Nat`. Derives `∀ k, le (abs (a
/// k)) (b k)` from the two pointwise hypotheses via
/// [`CRealPrelude::abs_le`]: its second premise `neg (a k) ≤ b k` comes from
/// `neg (a k) ≤ zero` ([`CRealPrelude::neg_le_neg`] at `0 ≤ a k`, rewritten
/// along `Equiv (neg zero) zero` via [`neg_zero_equiv`] and
/// [`CRealPrelude::le_congr`] — [`super::power`]'s identical pattern) chained
/// through `zero ≤ b k` ([`CRealPrelude::le_trans`] of the two pointwise
/// hypotheses) by one more `le_trans`. Then
/// [`declare_sum_range_converges_of_dominated`] closes it directly.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_sum_range_comparison_test(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let nonneg_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let ax = d.apply(a, &[x]);
        let zero_c = czero(d, p);
        let leq = cle(d, p, zero_c, ax);
        d.pi_fv(x_fv, nat, leq)
    };
    let nonneg_fv = d.fresh_fvar();
    let nonneg = d.kernel().fvar(nonneg_fv);

    let dominates_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let ax = d.apply(a, &[x]);
        let bx = d.apply(b, &[x]);
        let leq = cle(d, p, ax, bx);
        d.pi_fv(x_fv, nat, leq)
    };
    let dominates_fv = d.fresh_fvar();
    let dominates = d.kernel().fvar(dominates_fv);

    let sum_b = d.const_app(p.sum_range, &[b]);
    let pred_b = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let conv_m = converges_applied(d, p, sum_b, m);
        d.lam_fv(m_fv, carrier, conv_m)
    };
    let conv_b_ty = exists_ty(d, p, carrier, pred_b);
    let conv_b_fv = d.fresh_fvar();
    let conv_b = d.kernel().fvar(conv_b_fv);

    let sum_a = d.const_app(p.sum_range, &[a]);
    let pred_a = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let conv_l = converges_applied(d, p, sum_a, l);
        d.lam_fv(l_fv, carrier, conv_l)
    };
    let target = exists_ty(d, p, carrier, pred_a);

    // pointwise_abs : ∀ k, le (abs (a k)) (b k).
    let pointwise_abs = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ak = d.apply(a, &[k]);
        let bk = d.apply(b, &[k]);
        let zero_c = czero(d, p);

        let h_nonneg_k = d.apply(nonneg, &[k]); // le zero ak
        let h_dom_k = d.apply(dominates, &[k]); // le ak bk

        // le (neg ak) (neg zero)
        let h_negle = d.lemma(p.neg_le_neg, &[zero_c, ak, h_nonneg_k]);
        let neg_ak = cneg(d, p, ak);
        let neg_zero = cneg(d, p, zero_c);

        // le (neg ak) zero, via neg_zero ~ zero — power.rs's own pattern.
        let h_negzero = neg_zero_equiv(d, p);
        let refl_negak = d.lemma(p.equiv_refl, &[neg_ak]);
        let h_negle_zero = d.lemma(
            p.le_congr,
            &[
                neg_ak, neg_ak, neg_zero, zero_c, refl_negak, h_negzero, h_negle,
            ],
        );

        // zero ≤ bk, from le_trans zero ak bk.
        let h_zero_le_bk = d.lemma(p.le_trans, &[zero_c, ak, bk, h_nonneg_k, h_dom_k]);

        // neg ak ≤ bk, from le_trans (neg ak) zero bk.
        let h_negle_bk = d.lemma(
            p.le_trans,
            &[neg_ak, zero_c, bk, h_negle_zero, h_zero_le_bk],
        );

        // abs ak ≤ bk.
        let h_abs = d.lemma(p.abs_le, &[ak, bk, h_dom_k, h_negle_bk]);
        d.lam_fv(k_fv, nat, h_abs)
    };

    // minor : ∀ M, Converges (sumRange b) M → target.
    let minor = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let hp_ty = converges_applied(d, p, sum_b, m);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let cauchy_b = d.lemma(p.converges_cauchy, &[sum_b, m, hp]);
        let result = d.lemma(
            p.sum_range_converges_of_dominated,
            &[a, b, pointwise_abs, cauchy_b],
        );

        let with_hp = d.lam_fv(hp_fv, hp_ty, result);
        d.lam_fv(m_fv, carrier, with_hp)
    };

    let proof_body = creal_exists_elim(d, p, carrier, pred_b, target, conv_b, minor);

    let ty = {
        let after_conv_b = d.arrow(conv_b_ty, target);
        let after_dom = d.arrow(dominates_ty, after_conv_b);
        let after_nonneg = d.arrow(nonneg_ty, after_dom);
        let over_b = d.pi_fv(b_fv, fn_ty, after_nonneg);
        d.pi_fv(a_fv, fn_ty, over_b)
    };
    let value = {
        let with_conv_b = d.lam_fv(conv_b_fv, conv_b_ty, proof_body);
        let with_dom = d.lam_fv(dominates_fv, dominates_ty, with_conv_b);
        let with_nonneg = d.lam_fv(nonneg_fv, nonneg_ty, with_dom);
        let over_b = d.lam_fv(b_fv, fn_ty, with_nonneg);
        d.lam_fv(a_fv, fn_ty, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_comparison_test,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Exists.intro Nat predicate witness proof`.
pub(super) fn exists_nat_intro(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    predicate: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let intro_name = p.rat.int.logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[nat, predicate, witness, proof])
}

/// `CReal.sumRange_seq_zero`/`CReal.sumRange_seq_succ` — the recursive
/// sample-rate law. See the module documentation for the closed form it
/// implies, why that closed form is not declared here, and why it would not
/// by itself be enough to reach `CReal.Cauchy`.
///
/// Both close by `Eq.refl` alone: `sumRange f Nat.zero` ι-reduces to `zero :=
/// ofRat Rat.zero`, and `seq (ofRat q) k` ι-reduces to `q`
/// ([`super::declare_of_rat`]); `sumRange f (succ n)` ι-reduces to `add
/// (sumRange f n) (f n)`, and `seq (add x y) k` ι-reduces (through
/// `CReal.add`'s own `mk (fun n => …) _` representative,
/// [`super::declare_addition`]) to `seq x (shift k) + seq y (shift k)`.
fn declare_sum_range_seq_equations(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    // sumRange_seq_zero : ∀ f k, Eq Rat (seq (sumRange f Nat.zero) k) Rat.zero.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_n = d.zero();
        let sf = d.const_app(p.sum_range, &[f, zero_n]);
        let lhs = sample(d, p, sf, k);
        let rat_zero = rzero(d, p.rat);
        let stmt = req(d, lhs, rat_zero);
        let proof = rrefl(d, rat_zero);
        let value = {
            let inner = d.lam_fv(k_fv, nat, proof);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        let ty = {
            let inner = d.pi_fv(k_fv, nat, stmt);
            d.pi_fv(f_fv, fn_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_range_seq_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // sumRange_seq_succ : ∀ f n k,
    //   Eq Rat (seq (sumRange f (succ n)) k)
    //          (add (seq (sumRange f n) (shift k)) (seq (f n) (shift k))).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let sn = d.succ(n);
        let sf_sn = d.const_app(p.sum_range, &[f, sn]);
        let lhs = sample(d, p, sf_sn, k);

        let sk = shift(d, k);
        let sf_n = d.const_app(p.sum_range, &[f, n]);
        let left_sample = sample(d, p, sf_n, sk);
        let fn_at_n = d.apply(f, &[n]);
        let right_sample = sample(d, p, fn_at_n, sk);
        let rhs = radd(d, left_sample, right_sample);

        let stmt = req(d, lhs, rhs);
        let proof = rrefl(d, rhs);

        let value = {
            let inner = d.lam_fv(k_fv, nat, proof);
            let over_n = d.lam_fv(n_fv, nat, inner);
            d.lam_fv(f_fv, fn_ty, over_n)
        };
        let ty = {
            let inner = d.pi_fv(k_fv, nat, stmt);
            let over_n = d.pi_fv(n_fv, nat, inner);
            d.pi_fv(f_fv, fn_ty, over_n)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.sum_range_seq_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}
