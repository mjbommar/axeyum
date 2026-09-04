# ADR-1607: the metric layer carries W2-2 and W2-3 — continuity, Bishop compactness, and the EVT generalize off ℝ at a measured cost

Status: proposed
Date: 2026-09-04
Lane: `metric-compactness`
Roadmap: W2-2 (continuity as a topological notion) and W2-3 (Bishop compactness and the EVT), both unblocked by ADR-1602

Index-summary: ADR-1602 chose the metric layer over open sets on one
measurement — `Metric.Complete` generalized off ℝ for the price of two bridge
lemmas that already existed — and predicted that W2-2 and W2-3 would follow
"with no further design decision". This lane tested that prediction by
building both. **It holds, and the cost is now measured rather than
predicted: 44 declarations, all axiom-free, of which 43 were admitted the
first time the kernel saw them.**
Continuity over an arbitrary pair of metric spaces cost **zero estimates** —
`CReal.UniformlyContinuousOn`'s `spec` field IS the metric predicate once
`M = N = Metric.creal`, so the bridge is four `And` projections. Bishop
compactness (total boundedness + completeness, no covers) and the Extreme
Value Theorem over an arbitrary totally bounded subset cost one genuinely
constructive lemma — an approximate finite maximum by cotransitivity — and
nothing else new. **The interval instance was the expensive third:** a
closed interval of ℝ is Bishop-compact, and getting there needed a clamp
lemma, a grid induction, and one `Rat.natDivSucc` scaling identity, 10
declarations in all. The payoff is exact: `Metric.creal_evt_approx_max` and
`Metric.creal_evt_approx_max_via_metric` are **the same interned `ExprId`**,
one proved through `CReal.supOn` and one through a net in an arbitrary metric
space. **Recommendation: keep the metric-first bet; it is paying. Record that
the general theorems are cheap and the INSTANCES are where the work is, which
is the opposite of the usual expectation and the thing to plan around.**
Index-status: proposed

## Context

[ADR-1602](adr-1602-the-metric-layer-first-then-pointfree-and-not-open-sets.md)
closed W0-3 by building the thing that was supposed to depend on it. Its
argument rested on one number: generalizing `CReal.converges_of_cauchy` off ℝ
into `Metric.Complete` cost two already-landed bridge lemmas and three
`Exists.rec`s. From that it concluded that W2-2 (continuity) and W2-3
(compactness and the EVT) "are all reachable from `Metric` with no further
design decision".

That is a prediction about work nobody had done. This lane did it.

The prediction was worth testing precisely because one data point is one data
point. `Metric.Complete` is an unusually favourable case: `Cauchy` and
`TendsTo` were *designed* in ADR-1602's own commit alongside the ℝ instance
that had to satisfy them. Continuity and compactness are not like that —
`CReal.UniformlyContinuousOn` was designed in 2026-07 for the integral, and
`CReal.evt_approx_max` was proved through the supremum machinery with no
metric space in sight. If the metric layer only generalizes the vocabulary it
introduced itself, the bet is not paying.

## The measurement

### What was built

`crates/axeyum-lean-kernel/src/metric/continuity.rs` (15 declarations),
`metric/compactness.rs` (19), `metric/interval.rs` (10). Forty-four
declarations, all in the existing `Metric.*` namespace, all admitted by
`Kernel::add_declaration`, all with an empty `Kernel::axiom_footprint`.

The `metric::` suite went from 17 tests to 29 and stays green in 89 s
(`--release`, `--test-threads=4`).

### 1. W2-2, continuity: the bridge costs nothing, and that is the finding

The library had two continuity vocabularies and they were parallel rather
than connected:

| existing | shape | stated over |
|---|---|---|
| `CReal.UniformlyContinuousOn F a b` | `Type`, a `modulus : Nat → Nat` field plus a `Prop` `spec` | one real interval |
| `CReal.ContinuousAt F x` | `Prop`, phrased through `CReal.Converges` | one real point |

Neither mentions a metric space. This lane states both over an **arbitrary
pair** of metric spaces, in `Metric.CauchyAt`/`Metric.Cauchy`'s own idiom (a
free `Nat → Nat` modulus with the `∃` exactly one level up), each with a
predicate-relativized `*On` twin:

```text
Metric.UniformlyContinuousWith M N F mu : Prop
Metric.UniformlyContinuous     M N F    := ∃ mu, …With M N F mu
Metric.ContinuousAtWith        M N F x k : Prop
Metric.ContinuousAt            M N F x  := ∃ k,  …With M N F x k
Metric.Continuous              M N F    := ∀ x, ContinuousAt M N F x
```

and proves the two bridges:

```text
Metric.continuous_of_uniformly_continuous :
  (M N : Metric) -> (F : M.carrier -> N.carrier) ->
  Metric.UniformlyContinuous M N F -> Metric.Continuous M N F

Metric.creal_continuous_on :
  (F : CReal -> CReal) -> (a b : CReal) ->
  CReal.UniformlyContinuousOn F a b ->
  Metric.ContinuousOn Metric.creal Metric.creal (Metric.Interval a b) F
```

**The cost of the second is four `And` projections and one application.** Its
`∃`-witness is `CReal.UniformlyContinuousOn.modulus F a b u` *verbatim* — no
reindexing, no rate arithmetic — and its proof is that same witness's `spec`
field applied to the four bounds. Nothing is estimated. Two independent
facts make that possible, and neither was arranged for it:

- `uc_spec_body` (written 2026-07 for the integral) already reads
  `|x−y| ≤ 1/(modulus n + 1) → |Fx−Fy| ≤ 1/(n+1)`, which is the metric
  predicate's shape at `M = N = Metric.creal`;
- `Metric.dist Metric.creal x y` δι-reduces to `CReal.abs (x + -y)`, which is
  what `Metric.creal_dist` pins.

So the metric predicate and the `CReal` one are **definitionally the same
proposition**. That is the strongest form the answer to W2-2 could take, and
it was not designed in — it fell out.

`metric_tests::the_bridges_modulus_is_load_bearing` keeps that from being an
accident of reading: it rebuilds the bridge with `fun n => n` in the modulus
slot, everything else identical, and requires a refusal, with the honest
modulus admitted in the same test as its positive twin.

**The implication runs one way, deliberately.** The converse — pointwise
continuity implies uniform continuity — is absent, not unproved. Pointwise
continuity supplies *some* modulus per point with no claim that one serves
all of them; extracting one is Heine–Cantor, whose usual proof is a finite
subcover argument this library declines (ADR-1602). Bishop makes uniform
continuity on a compact set the primitive notion for exactly this reason. The
module documentation is the record of why, and nothing in the file claims the
converse.

### 2. W2-3, Bishop compactness: expressible with no topology at all

Bishop's definition (*Constructive Analysis* §4.2) is **complete and totally
bounded**. Both halves are metric conditions:

```text
Metric.NetIn      M P g N := ∀ n i, Nat.le i (N n) → P (g n i)
Metric.NetCovers  M P g N := ∀ n x, P x → ∃ i, Nat.le i (N n) ∧
                                 M.dist x (g n i) ≤ 1/(n+1)
Metric.TotallyBoundedOn M P := ∃ N g, NetIn M P g N ∧ NetCovers M P g N
Metric.CompleteOn       M P := ∀ f, (∀ n, P (f n)) → Metric.Cauchy M f →
                                 ∃ L, P L ∧ Metric.TendsTo M f L
Metric.CompactOn        M P := TotallyBoundedOn M P ∧ CompleteOn M P
Metric.Compact          M   := TotallyBounded M ∧ Complete M
```

No open set, no family of subsets, no index type, no finite subcover. The
reviewer's constructive objection to open-set topology — membership
predicates behave badly without excluded middle — never arises, for the same
reason ADR-1602 gave: nothing here is a subset.

Two encoding decisions are worth recording because they were forced, not
chosen:

- **The net is `g : Nat → Nat → carrier` plus `N : Nat → Nat`, not a
  `List`.** The covering clause has to *produce* an index, and `∃ i,
  Nat.le i (N n) ∧ …` is one `Exists` over `Nat`, which this kernel
  eliminates into `Prop` freely; list membership is an inductive predicate
  that brings its own recursor. And the finite-maximum lemma the EVT runs on
  is an induction on `N` — over a list every `Nat.le` step would become a
  `List` step for no gain.
- **`NetIn` is a separate field, not a convention.** It is load-bearing
  twice: the EVT's witness is a net point, so `P x` comes from it directly,
  and uniform continuity is only assumed *on* `P`, so applying it to a net
  point needs it again. It also makes the net automatically inhabited (index
  `0` is always `≤ N n`), which is why the EVT needs no separate
  non-emptiness hypothesis — one Bishop's own statement carries.

### 3. The EVT over an arbitrary metric space, and what it does NOT assume

```text
Metric.evt_approx_max :
  (M : Metric) -> (P : M.carrier -> Prop) -> (F : M.carrier -> CReal) ->
  Metric.TotallyBoundedOn M P ->
  Metric.UniformlyContinuousOn M Metric.creal P F ->
  (n : Nat) ->
  ∃ x, P x ∧ ∀ y, P y → F y ≤ F x + 1/(n+1)
```

**The hypothesis is total boundedness alone. Completeness is never used.**
Saying so is worth more than hiding it behind the stronger hypothesis, and
`metric_tests::w2_3_compactness_types_render` asserts the rendered type
mentions neither `Metric.CompleteOn` nor `Metric.CompactOn` — a claim read
off the kernel, not off the source. `Metric.evt_approx_max_of_compact` states
the Bishop-shaped corollary on top, and is one `And.left`.

The one genuinely constructive step is `Metric.approxMaxUpTo`:

```text
Metric.approxMaxUpTo : (h : Nat -> CReal) -> (k N : Nat) ->
  ∃ j, Nat.le j N ∧ ∀ i, Nat.le i N → h i ≤ h j + 1/(k+1)
```

An *exact* maximum of `N+1` reals is not available — choosing which index
attains it decides comparisons between reals. An approximate one is, by
induction on `N` with one `CReal.lt_cotrans` split per step at the pair
`h j < h j + 1/(k+1)`. **The slack does not accumulate**: in the branch where
the new element wins, the previous witness is discarded rather than chained
through; in the branch where it loses, the old witness's bound is reused
verbatim. A naive formulation that chains both branches doubles the slack
each step and does not close.

The error budget is two halves of `1/(2n+2)`, fused by
`Metric.CReal.rateSplit` (`Rat.natDivSucc_add` then `Rat.natDivSucc_halve`),
and `metric_tests::the_evt_error_budget_needs_the_doubled_index` requires the
kernel to refuse the same identity at the undoubled index while admitting it
at the doubled one.

### 4. The interval instance is where the work actually was

This is the finding that changes how to plan the next items. The general
theorems above are cheap. The **instance** is not.

| piece | why it was needed |
|---|---|
| `Metric.CReal.addSubCancel`, `subLeOfLeAdd`, `negNonpos`, `zeroLeOfRat` | four rearrangements the reals prelude never names |
| `Metric.CReal.absSubMinLe` | the net is `min b (a + i/(n+1))`, and `NetIn` forces the clamp; this says clamping does not move a point of `[a,b]` away from its neighbour |
| `Metric.CReal.gridCover` | the rational grid covers the interval it spans — an induction with one cotransitivity split per step |
| `Metric.CReal.natRateScale` | `B·(n+1)/(n+1) = B/1`, which is a **theorem** here, not a rearrangement, because `Rat.natDivSucc` is deliberately not antitone in its index (ADR-0512) |

Two sub-findings inside that:

**The clamp is an obligation, not a convenience.** `a + i/(n+1)` runs past `b`
for large `i`, and `Metric.NetIn` requires every net point to satisfy the
predicate. Only an *upper* clamp is needed — `a + i/(n+1) ≥ a` already — so
one `min` and no `max`, and one clamp lemma instead of two.

**Which cotransitivity branch takes which index is not free.** In
`gridCover`'s step at bound `K+1`, the split is on `x < a + K/(n+1)` versus
`a + K/(n+1) < x + 1/(n+1)`, and the second branch takes index **`K`**, not
`K+1`. Cotransitivity's two alternatives overlap, and the arrangement that
makes progress is the one where the overlap is exactly the covering radius. A
split whose second branch only reproduces the step hypothesis is sound and
useless; that was the first thing tried on paper.

Every bound in this file goes through `CReal.abs_le_of_two_sided`, so no
magnitude is ever taken apart — which is what lets it avoid the `neg_add` law
this kernel does not have.

### 5. The instance claim, made a measurement rather than a reading

Two theorems, one statement:

```text
Metric.creal_evt_approx_max            -- proved through CReal.supOn
Metric.creal_evt_approx_max_via_metric -- proved through Metric.evt_approx_max
  : (F : CReal -> CReal) -> (a b : CReal) -> CReal.le a b ->
    CReal.UniformlyContinuousOn F a b -> (n : Nat) ->
    ∃ x, Metric.Interval a b x ∧
         ∀ y, Metric.Interval a b y → F y ≤ F x + 1/(n+1)
```

Their `ty` fields are built by separate code in two different modules, and
`metric_tests::the_interval_evt_is_the_metric_evt_at_one_type` asserts the
kernel holds **the same interned `ExprId`** for both, with
`Metric.evt_approx_max`'s own type in the same test as a non-vacuity control.

The first is `CReal.evt_approx_max` plus `And` bookkeeping: `Metric.Interval
a b x` δβ-reduces to `a ≤ x ∧ x ≤ b`, so the two conclusions differ only in
how the conjunctions associate and whether the two range hypotheses on `y`
are curried — four projections and two `And.intro`s, no estimate. That is
itself the measurement the question "is the specific EVT an instance of the
general one?" turns on, and it isolates the answer: **the conclusions were
never the obstacle. The hypothesis was.** `CReal.le a b` against
`Metric.TotallyBoundedOn Metric.creal (Metric.Interval a b)` is the whole
distance, and §4 is what closing it cost.

### 6. Cost, counted

| measure | value |
|---|---|
| Rust added, term-building + docs | 4,609 lines across three modules (1,286 + 2,060 + 1,263) |
| Rust added, tests | 710 lines in `metric/metric_tests.rs` |
| declarations added | **44** — 34 definitions/theorems in `continuity.rs`+`compactness.rs`, 10 in `interval.rs` |
| axioms in the footprint of any of the 44 | **0** |
| `metric::` suite | 29 tests, 88.95 s (`--release`, `--test-threads=4`); was 17 tests / 58 s |
| slowest single declaration | `Metric.approxMaxUpTo`, 373 ms |
| all 44 declarations, kernel time | under 1.1 s total; the 90 s the suite takes is the `creal`/`cpoint` preludes underneath |
| declarations admitted the first time the kernel saw them | **43 of 44.** `continuity.rs` (15) and `interval.rs` (10) landed whole on their first kernel run. The one refusal was `Metric.approxMaxUpTo` (§7); the four declarations queued behind it in that run were never reached, and landed on their first look. |

Lemmas built here because the reals prelude does not have them — each a real
gap, not a stylistic preference:

| built here | why the prelude did not have it |
|---|---|
| `Metric.CReal.leAddOfSubLe` / `subLeOfLeAdd` | there is no "move a term across `≤`" pair; `Metric.CReal.leOfSubNonpos` is the `e = 0` instance of the first |
| `Metric.CReal.subAddCancel` / `addSubCancel` | `(u−v)+v ~ u` and `(v+e)−e ~ v` had no names |
| `Metric.CReal.ltAddRate` | `t < t + 1/(k+1)` — the only strict-order fact this development consumes |
| `Metric.CReal.rateSplit` | `1/(2n+2) + 1/(2n+2) = 1/(n+1)` lifted from `Rat` to `CReal` |
| `Metric.CReal.negNonpos`, `zeroLeOfRat` | sign facts about `ofRat` that no consumer had needed in this shape |
| `Metric.CReal.natRateScale` | see §4 |

### 7. One methodological finding, and it cost the lane an hour

**Three proof terms had `pi_fv` where they needed `lam_fv`.** A `∀ i : Nat, (fun h => …)`
is a `Pi` whose body is a lambda, and the kernel reports that as
`NotASort { got: ExprId(31391581) }` — which, like `UnboundFVar`, names
nothing. `build_metric_prelude` is a straight line of seventy-odd `declare_*`
calls, so the first symptom was not an error at all: it was a typecheck that
ran for ten minutes while growing a gigabyte of RSS every thirty seconds, on
a shared box, and would have been OOM-killed.

The fix in the tooling is small and general: `declare_all` in both new
modules now runs its declarations from a `[(label, fn)]` table and, under
`AXEYUM_METRIC_TIMING=1`, prints one line per declaration with its wall clock
and whether the gate accepted it. That located the culprit in a single run
and gave §6's per-declaration timings for free. **Any straight-line
`declare_*` sequence long enough to hide a slow member should carry the same
table.** Prose attribution does not work here — this repository has three
recorded instances of a wrong attribution for a slow build being propagated
in a brief before anyone measured.

The second half of the finding is about the mutation discipline. ADR-1602
recorded that a *record field* mutation cannot kill exactly one test, because
one bad declaration poisons the shared memoised prelude. The same applies to
every declaration in this file: mutating `Metric.approxMaxUpTo` kills all 29
tests, not one. So the criterion applied here is the other one — **every
negative control has a positive twin in the same test, built by the same
helper with one flag flipped** — and all four new controls satisfy it:

| control | mutation | positive twin |
|---|---|---|
| `the_bridges_modulus_is_load_bearing` | `fun n => n` in the bridge's modulus slot | the real `uc_modulus`, admitted |
| `uniform_to_pointwise_does_not_transpose_its_points` | `hmu n y x hd` for `hmu n x y hd` | the honest order, admitted |
| `the_evt_error_budget_needs_the_doubled_index` | index `n` for `2n+1` in the rate split | the doubled index, admitted |
| `the_interval_predicates_two_bounds_are_not_interchangeable` | `And.intro` given `x ≤ b` and `a ≤ x` transposed | the honest order, admitted |

And two coverage tests derive their subject from the authority rather than
from a literal: `every_metric_namespace_declaration_is_accounted_for` walks
`Kernel::environment` and fails if any `Metric.*` declaration is missing from
the test file's list, and the three `*_names_are_distinct_and_counted` tests
pin the size of each module's name struct and that no two of its fields
interned to one name.

## Decision

**Keep the metric-first bet. It is paying, and the shape of the payment is
now known: the general statements are cheap and the instances are
expensive.**

1. **W2-2 and W2-3 are closed.** Continuity is a metric notion with the ℝ
   development connected to it rather than parallel to it; Bishop compactness
   is stated and the closed real interval satisfies it; the EVT holds over an
   arbitrary totally bounded subset of any metric space and the interval EVT
   is literally an instance of it.
2. **ADR-1602's prediction is confirmed on a second and third case, and the
   confirmation is stronger than the original.** `Metric.Complete` generalized
   vocabulary ADR-1602 introduced itself. `Metric.ContinuousOn` generalizes
   `CReal.UniformlyContinuousOn`, designed in 2026-07 for the integral by
   people who were not thinking about metric spaces, and the bridge still
   costs zero estimates. That is the case that could have failed and did not.
3. **Plan for the instance, not for the theorem.** The general EVT is 19
   declarations including its own supporting lemmas; the interval instance is
   10 more, and it is where every hard step lives (the clamp, the grid
   induction, the `natDivSucc` scaling identity). Anyone sizing "prove X over
   a general metric space, then instantiate at ℝⁿ" should budget the
   instantiation at least as heavily as the theorem. This is the opposite of
   the usual expectation.
4. **Do not add an open-set carrier to serve compactness.** Nothing in this
   lane wanted one. Every compactness statement here is a conjunction of two
   metric conditions, and the EVT's proof is a net plus a finite approximate
   maximum. ADR-1602's §"Do not build open-set topological spaces at all"
   stands, now with the compactness case actually built rather than argued.

## What changes downstream

| item | before | after |
|---|---|---|
| **W2-2** — continuity as a topological notion | depends on W2-1 (ADR-1602 restated it) | **closed.** `Metric.Continuous*`, `Metric.UniformlyContinuous*`, `Metric.creal_continuous_on`. The uniform ⇒ pointwise arrow is one-way and documented as such. |
| **W2-3** — Bishop compactness on intervals, EVT as an instance | unblocked, not started | **closed.** `Metric.CompactOn`, `Metric.creal_compactOn_interval`, `Metric.evt_approx_max`, and the two-proofs-one-`ExprId` instance pin. |
| **W2-10** — products and subspaces | split by ADR-1602; the product buildable, the subspace blocked on `Subtype` | the *subspace* half is now demonstrated rather than recommended: every `*On` statement here is relativized to a predicate and the interval instance shows the idiom carries a real theorem. The `Subtype` blocker is unchanged and still real. |
| **W2-21** — a topological-space carrier as a frame | not on the critical path | unchanged, and one more reason it is not: compactness did not need it. |
| **reviewer 06 topology** | 49 declarations, items 1–2 done | 93 declarations; Next-Five items 3 and 4 (continuity, compactness) are done. |
| **reviewer 03 classical analysis** | "blocked behind topology" weakened by ADR-1602 | weakened further: the EVT, the one classical-analysis theorem the roadmap names under W2-3, is now general. |
| **the metric layer's next instance** | — | the obvious one is `Metric.cpoint` (the Euclidean plane): it has no completeness theorem and no compact subsets. §4 says what that will cost — the general statements are already there, and the work will be entirely in the instance. |

## Consequences

- The library's topology shelf goes from 49 declarations to 93, and from one
  theorem that holds of every metric space to a continuity layer, a
  compactness layer, and an Extreme Value Theorem that do.
- The claim "`CReal.evt_approx_max` is an instance of a general theorem" is
  now checkable by a test that compares two interned `ExprId`s, rather than
  by reading two statements and judging them similar. That is the form this
  kind of claim should take everywhere; a rendered-string comparison would
  have passed on statements that merely looked alike.
- A second prediction of ADR-1602 is confirmed in passing: `Exists`'s
  `Prop`-only elimination is never an obstruction here either. Every one of
  the eleven `Exists.rec`s in this lane — the net, its count, the modulus,
  the approximate maximiser, the covering index, the Archimedean bound —
  eliminates into a `Prop` goal. The price is that none of those witnesses is
  available as data: `Metric.TotallyBoundedOn` cannot hand a consumer the net
  to compute with. A `Type`-valued total boundedness would need a `Sigma`,
  and this kernel has none.
- The failure mode in §7 is worth generalizing beyond this file. **A long
  straight-line builder turns a local typing error into a global performance
  mystery.** The label table costs four lines and converts it back into a
  local error with a name.
