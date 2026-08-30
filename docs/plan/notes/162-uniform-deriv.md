# Notes: 162-uniform-deriv

Detail moved out of [`../status/162-uniform-deriv.md`](../status/162-uniform-deriv.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

   **Lane 159's plan did not anticipate this, and without it the construction
   is unstateable.** `abs_diff_le_of_deriv_bound` requires `le x y`, because
   `monotone_of_nonneg_deriv` orders its endpoints — but `deriv_spec_body`
   quantifies `x` and `y` independently over `[a, b]` and never orders them,
   and `le x y ∨ le y x` decides the sign of a real. Every route through the
   ordered form needs that dichotomy.

   The fix uses **no case split at all**: `u := min x y` is below both
   endpoints and inside `[a, b]` (`le_min` from `a ≤ x`, `a ≤ y`), so the
   ordered inequality applies to `(u, x)` and `(u, y)` separately with no
   knowledge of which endpoint is larger, and the triangle through `F u`
   gives `|F y − F x| ≤ M·((y − u) + (x − u))`. The constant stays **exact**
   rather than doubled because `(y − u) + (x − u) ≤ |y − x|` follows from the
   meet's universal property alone — three `le_min` applications whose legs
   are `le_abs_self`, `neg_le_abs` + `neg_sub_swap`, and `abs_nonneg`. `min`
   is never unfolded to its pointwise `Rat.min` representation, and the
   development has no `max − min = |·|` identity (it would not be derivable
   from `min_le_left`/`min_le_right`/`le_min` if it were needed).

   The one new hypothesis, `le zero M`, is not removable — the last step
   multiplies the domain bound through by `M` — but is free for every caller.

2. `CReal.abs_diff_sub_le_of_deriv_bound` — the tail estimate, in the shape
   leg (A) consumes:

       ∀ F F' G G' a b, HasDerivativeOn F F' a b → HasDerivativeOn G G' a b →
       ∀ M, le zero M →
       (∀ z, le a z → le z b → le (abs (add (F' z) (neg (G' z)))) M) →
       ∀ x y, le a x → le x b → le a y → le y b →
       le (abs (add (add (F y) (neg (F x))) (neg (add (G y) (neg (G x))))))
          (mul M (abs (add y (neg x))))

   `hasDerivative_sub`, then (1), then one commutative-group rearrangement.
   `hasDerivative_sub` builds its functions as `fun r => add (F r) (neg (G r))`
   **verbatim**, so the derivative bound needs no transport at all, only
   re-wrapping — every application beta-reduces to the shape the hypothesis
   already has. The rearrangement `(F y − G y) − (F x − G x) ~
   (F y − F x) − (G y − G x)` is the whole algebra: the Lipschitz bound is
   about the difference FUNCTION at two points, the series argument needs the
   difference of two INCREMENTS.

3. `CReal.hasDerivative_uniform_limit`, above.

**The sizing held, and the characterisation was accurate.** Lane 159 sized
step 2 at "comparable to `hasDerivative_mul` (~1,000 lines)". The landed diff
is **1,201 insertions** across the three declarations (496 for (1) + its four
helpers, 372 for (2), 817 for (3) minus registration). The three-way
`1/(3e+3)` split worked exactly as characterised, and the
`abs_diff_le_of_deriv_bound` tail step worked — through (1) rather than
directly, which is the one correction to the plan.

**The refutation of the finite-partial-sum shortcut is load-bearing and was
respected.** Leg (A) is bounded by uniform convergence of the FUNCTIONS only
by a constant `2δₙ`, useless against `deriv_spec_body`'s `ε·|y − x|` budget
over `y` arbitrarily close to `x`; it goes through (2) on the tail `Fₖ − Sₙ`
with `le_of_forall_le_add_small` removing the `k → ∞` slack.

**The accuracy bookkeeping, for whoever builds on this.** `sidx e := 3e+2` is
written as `scaled_index` at `k := 2` rather than hand-built, because
`Rat.natDivSucc_scale`'s own index `(c+1)·m + c` **is** `3e+2` at `c := 2` —
so the three-legs-to-one fusion is that lemma plus `Rat.natDivSucc_add`
twice, with no separate identity. The sequence index
`nidx e := scaled_index r' (sidx e)` is `weaken_rate`'s index, so that
function's own proof is reused verbatim for "the derivative series' rate at
`nidx e` is at most `1/(3e+3)`". `|y − x| ≤ 1` (from the spec's own closeness
hypothesis via `Rat.natDivSucc_le_one`) is what lets the two function legs of
(A) be paid in a purely rational budget.

**Kernel rejections: none.** All three declarations were accepted on the
first `add_declaration`. The only iteration was Rust-level: `radd` takes
`(d, a, b)` and was called `(d, rat, a, b)` at four sites. That matches the
standing observation that the borrow checker and arity, not the kernel,
are what reject.

**What this does NOT give you.** It is stated over an arbitrary sequence and
does not, by itself, differentiate any named series. Reaching
`HasDerivativeOn cosFnWide (fun x => neg (sinFn x))` still needs lane 159's
remaining steps 1 and 3: `∀ n, HasDerivativeOn Sₙ Sₙ' 0 (8/5)` for cosine's
partial sums (an induction over `hasDerivative_add` with the index-shifted
coefficient identity `cosTerm (j+1)·(2j+2) ~ −sinTerm j`), and
`hasDerivative_congr` to move from `succ n`-indexed partial sums to the named
functions. Nothing in this theorem inspects a sequence element — every fact
used about `F`/`F'` is one of the two `UniformConvergesOn.spec`s or the
per-index `HasDerivativeOn` — so it applies verbatim once those exist.

**Timings** (this host, load 3–8). `creal_prelude_builds`: 101.74 s after (1),
91.09 s after (2), **92.18 s** after (3) — inside the recent 94–117 s band and
with no measurable cost from any of the three; the spread across the three
runs is load, not content.
`every_creal_declaration_is_checked_and_axiom_free` (`--release`) 19.19 s,
green — and that test derives coverage from `kernel.environment()` directly,
in both directions, so it is what confirms all three are present and
axiom-free rather than merely listed. `clippy --all-targets --all-features -D
warnings` green. `shape_search` rebuilt fresh for both the before and after
readings, so the stale-prebuilt false-ABSENT hazard does not apply to either.

**Nine `pub(super)` extractions, no duplication.** `hd_ty`,
`deriv_spec_body`, `abs_le_of_equiv`, `cancel_middle`, `esymm`, `erefl`,
`echain`, `neg_mul_equiv_left`, `swap_middle_pair` and the `cadd`/`cneg`/
`cmul`/`cabs`/`czero` builders are now `pub(super)` in `creal/derivative.rs`
and imported by `creal/uniform_convergence.rs` rather than copied. The two
genuinely new general helpers — `le_shift` (the linear shuffle
`p − q ≤ r ⟺ p − r ≤ q`, called seven times) and `abs_sub_flip` (`|u − v| ≤ q`
to `|v − u| ≤ q` through the two-sided form, since
`Equiv (abs (neg x)) (abs x)` is deliberately absent) — are candidates for
promotion if a third consumer appears.
