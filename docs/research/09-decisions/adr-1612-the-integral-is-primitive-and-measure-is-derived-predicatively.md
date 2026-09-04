# ADR-1612: the integral is primitive and measure is derived, on a predicative pre-integration space

Status: proposed
Date: 2026-09-04
Lane: `integration-space`
Roadmap: W3-1 (measure and the Lebesgue integral on ℝ, convergence C5) — reviewers 03.4 and 08.5

Index-summary: W3-1 is the department's largest shelf and the gate on
reviewers 03 and 08. The brief's thesis was **do not build measure theory;
build an integration space and derive measure from it**, and the proposed
deciding number was *how many existing `CReal.integral` theorems become
instances of a general statement rather than needing reproof*. That number was
measured and **it is 1 of 63** — the thesis's own metric returns almost
nothing, because the theorems the brief expected to absorb are precisely the
ones that become the record's AXIOMS. The right denominator is 6, not 63:
exactly six of `creal/integral.rs`'s 63 declarations are statements about the
integral *as a linear functional*, five of them are the record's law fields
and the sixth (`integral_witness_independent`) is the one that is derived —
verified by a test that compares the two rendered types and requires them
**equal**. **The decision is nonetheless integral-first**, on a different and
larger measurement: 70 declarations, empty footprints, **three instances**
(the Riemann integral on `[a,b]`, `CReal.sumRange` over a finite index set,
and the Dirac probability space), a measure layer derived from the integral,
five theorems that are NEW on ℝ, and the same five landing on `CReal.sumRange`
and on the Dirac space at zero marginal cost. A fourth design constraint is
adopted alongside setoids (ADR-1595), hypotheses-not-axioms (ADR-1601) and
metric-first (ADR-1602): **predicativity**. What was built is a
*pre-integration space* in the sense of Petrakis and Zeuner
(arXiv:2207.08684), not a Bishop–Cheng integration space, and it arrived there
by the "axioms from what the integral actually proves" discipline before the
paper was read — cost of switching to the predicative design: **zero, nothing
to switch**. L¹ as the completion is NOT built, and the reuse number the
completion turns on is measured: **the completeness STATEMENT is reusable in
principle (5 generic `Metric.*` declarations) but 0/5 in practice, because
`Metric.dist` is total and integrability is `Sort 1` data that `Sigma`'s
absence forbids bundling into the carrier — the SAME absence ADR-1595 measured
for quotients and this ADR met again for integrable sets, three independent
hits; and the completion CONSTRUCTION is 0/78, because this kernel has no
completion functor at all.** One blocker this lane wrote down was then
**refuted by its own tool and closed**: `|·|`-closure of the integrable
functions has no NAME in ℝ but is two lemmas away as a STEP, and
`IntSpace.CReal.uniformly_continuous_abs` now exists.
Index-status: proposed

## Context

Reviewer [03 — classical analysis](../../math-department/03-classical-analysis.md)
is recorded as **unmoved**, and their sentence is the one to keep in view:

> "You have a very careful Riemann integral. I have not used a Riemann
> integral since graduate school."

Reviewer [08 — probability and statistics](../../math-department/08-probability-and-statistics.md)
is blocked behind the same shelf: everything past the weak law needs measure.
The roadmap's own W3-1 row records that ADR-1602 **explicitly did not settle**
this dependency.

The classical route is measure first, integral second. Bishop's is the
inverse: the integral is primitive and the measure of a set is the integral of
its indicator, *when that indicator is integrable*. The brief's argument for
trying the inverse here was empirical rather than philosophical — the library
already had most of an integration space and called it Riemann integration.
`CReal.integral` carries linearity (`integral_add`, `integral_scale`,
`integral_const`), monotonicity (`integral_le`), the absolute bound
(`integral_abs_le`), additivity over splitting, both directions of the FTC,
and integration by parts, and none of the first four mentions a Riemann sum in
its statement.

### The correction that arrived mid-build, and what it cost

The brief named Bishop–Cheng integration spaces. Bishop–Cheng's L¹ is
**impredicative**: the space of integrable functions is defined by quantifying
over what is constructively a proper class. Petrakis and Zeuner (*Pre-measure
spaces and pre-integration spaces in predicative Bishop–Cheng measure theory*,
arXiv:2207.08684, 2022) is the repair, and it replaces the class quantification
with **set-indexed families**.

This kernel has a universe hierarchy and no impredicative trick, so a faithful
transcription of Bishop 1972 would have hit a predicativity wall rather than a
constructivity one. **It did not, and the reason is worth recording**: the
brief's other instruction — *decide the axioms from what the existing integral
actually proves, not from a textbook* — produced the predicative structure
directly. The record's `Integrable : carrier → Sort 1` is a set-indexed family
over a fixed carrier; the convergence axiom, which is where Bishop–Cheng's
impredicativity lives, is absent, because `CReal.integral` does not prove it.
**Cost of switching to the predicative design: zero. There was nothing to
switch.** The two honest gaps between what is built and Petrakis–Zeuner's
definition are named under *Consequences*.

## The measurement

### What was built

`crates/axeyum-lean-kernel/src/intspace.rs` and five submodules, commits
`63c9a000d` (the record, the generic layer, the measure layer, the convergence
family, two instances) and `9d47af7e4` (detachable subsets, counting measure,
the Dirac space). **70 declarations** in a new `IntSpace` namespace, every one
admitted by `Kernel::add_declaration`, **every axiom footprint empty**, 14
tests green in 79 s.

`IntSpace` is a **sixteen-field `Sort 2` record** built with the `AlgS` spine's
`declare_record` — the same machinery, and for the same reason, as ADR-1602's
`Metric`: `CReal`'s equality is the defined relation `CReal.Equiv` and not the
kernel's primitive `Eq` (ADR-0512).

| # | field | type |
|---|---|---|
| 0 | `carrier` | `Sort 1` — the functions being integrated |
| 1 | `fle` | `carrier → carrier → Prop` |
| 2–3 | `fleRefl` / `fleTrans` | the preorder laws |
| 4–6 | `fadd` / `fscale` / `fconst` | the linear structure and the constants |
| 7 | `constMono` | `∀ x y, CReal.le x y → fle (fconst x) (fconst y)` |
| 8 | `Integrable` | `carrier → Sort 1` |
| 9 | `constIntegrable` | `∀ c, Integrable (fconst c)` |
| 10 | `integral` | `∀ f, Integrable f → CReal` |
| 11 | `total` | `CReal` |
| 12 | `integralConst` | `∀ c h, Equiv (integral (fconst c) h) (mul c total)` |
| 13 | `integralLe` | `∀ f g hf hg, fle f g → le (integral f hf) (integral g hg)` |
| 14 | `integralAdd` | `∀ f g hf hg hfg, Equiv (integral (fadd f g) hfg) (add (integral f hf) (integral g hg))` |
| 15 | `integralScale` | `∀ c f hf hcf, Equiv (integral (fscale c f) hcf) (mul c (integral f hf))` |

Three entries in that table are decisions rather than transcription.

**`Integrable` is `Sort 1`, not `Prop`.**
`CReal.UniformlyContinuousOn` is a `Type` — a modulus paired with its spec —
because `CReal.integral` *consumes* the modulus to compute the value. An
integration space over this kernel therefore cannot make integrability a
proposition without losing the integral. That decision propagates: an
integrable set cannot be bundled into one object, because `Sigma` and
`Subtype` are absent from this kernel (ADR-1595's own finding) and
`structures::declare_record` is fixed at `Sort 2`, whose universe control
asserts as much. So an integrable set is carried as a `Sort 1` integrability
datum plus a `Prop` side condition, two arguments instead of one. **Measured
cost: one extra binder per theorem, and nothing else** — the same answer
ADR-1601 got for classical hypotheses.

**Every integral law takes its own integrability witnesses explicitly**, the
shape `CReal.integral_add` and `CReal.integral_scale` already have. The
alternative — closure fields (`Integrable f → Integrable g → Integrable (fadd
f g)`) — is a *stronger* axiom than any existing theorem proves, and it is not
needed: witness independence makes the choice immaterial and is **derived**
here rather than assumed.

**`fconst` and `total`, not a `fone` and a lattice.** The library's evaluation
law is `CReal.integral_const`, `∫c = c·(b−a)`. Making the constant embedding
and the whole space's measure fields turns that one existing theorem into
field 12 verbatim.

### The deciding number, and why the brief's own metric is the wrong one

The brief asked: *how many of the existing `CReal.integral` theorems become
instances of a general statement rather than needing reproof?* Here is the
partition of all **63** declarations in `creal/integral.rs`'s inventory shard
(the authority, not a name grep):

| class | count | what it is |
|---|---|---|
| **A — became the record's AXIOMS** | **5** | `integral`, `integral_const`, `integral_le`, `integral_add`, `integral_scale`. The `crealInterval` instance fills fields 10, 12, 13, 14, 15 with these, applied to `a`, `b`, `hab`, and no new estimate. |
| **B — RE-DERIVED as an instance** | **1** | `integral_witness_independent`. |
| **C — blocked on two more fields** | **3** | `integral_abs_le`, `integral_abs_le_of_bound`, `integral_sub_linear_le`. Each needs `\|·\|` and negation on the carrier. The `\|·\|`-closure obligation is now dischargeable (`IntSpace.CReal.uniformly_continuous_abs`, below); what remains is `CReal.neg (CReal.mul x y) ~ CReal.mul (CReal.neg x) y`, which the ℝ prelude has under no name — `neg_mul_neg` is the squares-only special case. |
| **D — structurally outside ONE space** | **14** | the splitting family, the FTC pair, `integral_by_parts`, `antiderivative`, `integral_converges`, `riemannSum_integral_close`. Each relates several integration spaces or varies the endpoint. |
| **E — Riemann-sum construction** | **40** | `riemannSum*`, `mesh*`, `fineSample*`, the reblocking and Cauchy machinery. Not statements about the integral at all. |

**So the answer to the brief's question is 1 of 63, and that is a partial
refutation of the brief's framing, not a confirmation of it.** The theorems it
expected the general layer to absorb are exactly the ones that turn out to be
irreducible per-instance obligations. A record whose axioms are taken from
what a development proves cannot then re-derive what it took.

The number becomes intelligible with the right denominator. Six of the 63 are
statements about the integral *as a linear functional on an ordered set of
functions*; the other 57 are either the construction (E) or about several
spaces at once (D) or need structure the record deliberately lacks (C). Of
those **6, five are axioms and one is derived.** That ratio is what an
axiomatisation is supposed to look like — a minimal law set plus everything
else — and it is a healthy result rather than a disappointing one, but it is
not the result the brief predicted, and it does not by itself justify the
work.

**B is verified, not asserted.** `IntSpace.CReal.integral_witness_independent`
is declared with a proof that is `IntSpace.integral_witness_independent`
applied to `IntSpace.crealInterval a b hab` and nothing else, and the test
`the_rederived_statement_equals_creals_own` renders both its type and
`CReal.integral_witness_independent`'s and requires them **equal as strings**.
A weaker or differently-quantified statement fails that test.

### What actually justifies integral-first

Not retirement of existing theorems. Four other things, each measured:

**1. Three instances, and they share no machinery.**

- `IntSpace.crealInterval a b hab` — the Riemann integral on `[a,b]`. Twelve
  of sixteen fields are an existing `CReal` declaration applied to `a`, `b`,
  `hab`; the remainder are the pointwise definitions and a three-line
  `constMono`.
- `IntSpace.crealFinite m` — `CReal.sumRange` over `Nat.succ m` indices,
  filled by `sumRange_le`, `sumRange_add`, `mul_sumRange`, `sumRange_const`.
- `IntSpace.crealDirac k` — evaluation at `k`, `total = 1`. A **probability**
  integration space; every law field is `CReal.Equiv.refl` or one lemma.

One is built from Riemann sums with a modulus, one from a `Nat.rec`, one from
nothing at all. Each carries a reduction probe proved by `CReal.Equiv.refl`,
so its admission *is* the statement that the selector reduces definitionally
on the instance — `Metric.creal_dist`'s probe, transplanted.

**2. Five theorems that are NEW on ℝ**, none previously provable:
`integral_congr` (a two-sided pointwise bound gives an `Equiv` of integrals —
derived from `integral_le` alone by antisymmetry, a step nobody took in the
eight days `integral_le` existed), `integral_nonneg`, `integral_le_const`,
`const_le_integral`, `integral_le_total`. Two are landed as explicit
`IntSpace.CReal.*` declarations whose statements do not mention `IntSpace` at
all — asserted by the test, which requires the rendered type to contain
`CReal.integral` and **not** contain `IntSpace`.

**3. The same five land on `CReal.sumRange` at zero marginal cost.**
`IntSpace.CReal.sumRange_congr` and `sumRange_nonneg` are the *same* generic
theorems at the finite instance. This is the arrow reviewer 08 is waiting on:
**a finite index set is an integration space**, expectation is an integral,
and `total` is the index count, so the derived measure is counting measure and
the Dirac space is its probability normalisation.

**4. Measure is derived, in five declarations.**
`IntSpace.measure S chi h := S.integral chi h`, with `measure_nonneg`,
`measure_le_total`, `measure_witness_independent` (*the measure of a set does
not depend on which integrability datum witnesses it* — on a classical
development this is not even a statement), `measure_const` and `measure_univ`.

### Integrable sets are positive, and the undecidability objection dissolves

Reviewer 03's objection is that membership in a measurable set is undecidable,
so indicators are not `Bool`-valued. Both halves of the answer are built.

The **general** notion is `IntSpace.Indicator S chi := 0 ≤ chi ≤ 1`, paired
with the `Sort 1` datum `S.Integrable chi`. It is deliberately the *located*
condition and not idempotence (`chi·chi ~ chi`): over ℝ, `x·(x−1) ~ 0` does
**not** give `x ~ 0 ∨ x ~ 1`, because a vanishing product of reals does not
decide which factor vanished. So a general indicator here really is
`[0,1]`-valued — the objection confirmed, not worked around.

The **base case** is where the objection dissolves, and it is Petrakis and
Zeuner's own starting point: a **detachable** subset has decidable membership,
is literally a `Nat → Bool`, and its indicator
`IntSpace.detachableIndicator A := boolIndicator ∘ A` is a genuine function
that computes.
`IntSpace.detachable_is_indicator : ∀ A m, Indicator (crealFinite m)
(detachableIndicator A)` says **every detachable subset of a finite index set
is an integrable set**, with `IntSpace.Triv.mk` as its datum and nothing
discharged at the use site; `IntSpace.dirac_measure_detachable` computes the
Dirac measure of one by `CReal.Equiv.refl`.

What is **not** built is complemented subsets of ℝ, and the reason is
structural rather than unfinished work: an integrable set of `crealInterval`
needs a uniformly continuous indicator, and a uniformly continuous
`{0,1}`-valued function on a connected interval is constant. That is precisely
why Petrakis–Zeuner take L¹ to be the **completion** of the pre-integration
space rather than the pre-integration space itself.

### Convergence, as an ADR-0603 graded family

| grade | declaration | status |
|---|---|---|
| general constructive form | `IntSpace.integral_mono_step`, `IntSpace.integral_seq_le` | **proved**, footprint empty |
| classical form, on a hypothesis | `IntSpace.monotone_convergence_of_real` | **proved**, footprint empty, **cost: one binder** |
| the classical principle itself | `IntSpace.RealMonotoneConvergence` | a `Prop`, never asserted |
| boundary refutation | — | **NOT LANDED**; obstruction named below |

The constructive content of monotone convergence is entirely in the integral:
if `u₀ ≤ u₁ ≤ … ≤ f` pointwise then `∫u₀ ≤ ∫u₁ ≤ … ≤ ∫f`, and each half is
one application of `integralLe`. What is *not* constructive is the last step,
and it is not about integration: **a bounded monotone sequence of reals need
not converge.** That is LPO-strength, so the classical theorem is stated
ADR-1601's way — the principle as an explicit hypothesis, never an axiom — and
the measured cost of carrying it is **one binder and one argument position**,
matching ADR-1601's own ten-theorem number exactly.

**The boundary refutation did not land, and the obstruction is one lemma.**
The converse (*unrestricted monotone convergence on a space with `total ~ 1`
implies `RealMonotoneConvergence`*) is true — feed the space `u n := fconst (s
n)` — but it needs to transport `CReal.Converges` along a **pointwise** `Equiv`
between two sequences, and the ℝ prelude has no such congruence.
`converges_of_equiv` is about a sequence exactly `Equiv` to a fixed *target*;
`converges_of_close` wants a `Within` bound on the raw samples;
`converges_unique` is about two limits of one sequence. The missing statement
is `∀ n, Equiv (f n) (g n) → Converges f L → Converges g L`, it belongs in
`creal/convergence.rs`, and this lane was scoped out of `creal/`.

### The L¹ completion: what it would reuse, measured

This is the number the correction asked for, and it is measurable without
building L¹.

**First, a blocker this lane wrote down and then refuted with its own tool,
because the sequence is the point.** The L¹ seminorm is `‖f−g‖₁ = ∫|f−g|`, so
the integrable functions must be closed under `|·|`; Petrakis–Zeuner's `L` is
closed under the lattice operations for the same reason. A search of the
542-name `CRealPrelude` field list finds no `uniformly_continuous_abs`, with
`uniformly_continuous_add`, `_mul`, `_neg` and `_const` as positive controls —
and that was written into a draft of this ADR as the one lemma blocking L¹.
It is false. `shape_search --include-constructed --concl
CReal.UniformlyContinuousOn` (declarations=3653, verdict FOUND 17) shows the
closure table also holds `CReal.uniformly_continuous_max` and `_min`, declared
in `creal/ivt_boundary.rs` rather than in the file the name search covered;
and `CReal.abs x` is `CReal.max x (CReal.neg x)` **by definition**. So the
step is the composition of two existing lemmas and no new estimate.
`IntSpace.CReal.uniformly_continuous_abs` is declared here and admitted, which
is also the proof that `abs` really unfolds that way. *Search for the step,
not the name* — the rule, applied to a blocker this lane had itself written
down.

That leaves the real obstruction, and it is bigger.

| what | reusable in principle | reusable today | duplicated |
|---|---|---|---|
| the completeness **statement** | **5 / 5** — `Metric.CauchyAt`, `Metric.Cauchy`, `Metric.TendsToAt`, `Metric.TendsTo`, `Metric.Complete`, all generic over an arbitrary `Metric` | **0 / 5** | — |
| the completion **construction** | 0 / 78 | 0 / 78 | **78** — the `CReal` completion core (`creal/inventory/{base,convergence,completeness,speedup}.rs`, counted by inventory entry) |

**Why 0/5 today.** In the setoid style this development already uses, taking
`f ≈ g := Equiv (∫|f−g|) 0` would make L¹ a `Metric` in ADR-1602's exact
sense: `distSelf` and `distEquiv` hold definitionally, `distComm` from
`|f−g| = |g−f|`, `distTriangle` from `CReal.abs_add_le` plus `integralLe` and
`integralAdd`. It cannot be built, and the reason is structural.
**`Metric.dist` is TOTAL on the carrier** — `dist : carrier → carrier → CReal`
— while `∫|f−g|` needs the integrability data of `f` and `g`. The carrier
would have to be the total space of the family `Integrable`, i.e. a `Sigma`
type, and `Sigma` and `Subtype` are absent from this kernel.

That is the **third independent hit on one absence**: ADR-1595 measured it for
quotients, this ADR met it again for bundling an integrable set, and now for
the L¹ pseudometric. Three different shelves blocked by the same missing
declaration is a roadmap item with a measured justification, which none of the
three had on its own.

**Why 0/78 regardless.** `Metric` has completeness as a **predicate** and no
**functor**: nothing in this kernel takes a metric space to its completion.
`CReal` is the only completion in the tree and it is hand-built out of regular
sequences, `Within`, `speedup` and `regularity`, none of which is stated over
a `Metric`. Even with `Sigma`, L¹ would reuse every word of the *statement* of
its completeness and not one line of the *construction*.

So "build L¹" decomposes into two specific and independently useful items:
**`Sigma`/`Subtype` in the kernel** (three shelves waiting), and **a generic
completion of a metric space** (which would retro-fit `CReal` itself as its
first instance, the natural successor to ADR-1602's `Metric.creal_complete`).
Neither is measure theory, and both are reusable far outside it. That
decomposition is the most useful thing this lane produced for W3-1.

## Decision

**Build the shelf integral-first, on a predicative pre-integration space.**

1. **The integral is primitive and measure is derived.** `IntSpace.measure S
   chi h := S.integral chi h`, defined only where the integrability datum
   exists. Do not introduce a σ-algebra, a measurable-set predicate, or a
   measure as primitive data.
2. **Predicativity is a design constraint of this project**, alongside setoids
   (ADR-1595), classical-principles-as-hypotheses (ADR-1601) and metric-first
   (ADR-1602). Concretely: no definition may quantify over a collection that
   is not itself a set of the theory. Follow **Petrakis–Zeuner
   pre-integration spaces**, not Bishop–Cheng integration spaces; take the
   axioms from set-indexed families.
3. **Sets are complemented, and the base case is detachable.** A subset is
   positive data — the pair, or in the decidable case the `Bool`-valued
   function — never the failure of a decision. `IntSpace.Indicator` is the
   general located condition; `detachableIndicator` is the computing base
   case.
4. **L¹ is the completion, and it is deferred behind a generic completion.**
   Do not hand-build an L¹ completion. Build the metric-completion functor
   first; L¹ and a retro-fit of `CReal` are both instances.
5. **Classical convergence stays a hypothesis.** `RealMonotoneConvergence` is
   a `Prop` and is never asserted.

## What changes downstream

**For reviewer 03 (classical analysis).** Be plain about this: an integration
space is not their subject, and they may reasonably say so. They asked for the
Lebesgue integral with the three convergence theorems, and what exists is a
pre-integration space with monotone convergence graded. What they gain now is
(a) five new theorems about `CReal.integral` and a congruence that lets them
rewrite under an integral, (b) a measure that is defined rather than absent,
(c) a named, sized path to L¹ — one lemma to state the seminorm, one
construction (the metric completion) to build it — rather than an open-ended
"needs measure theory". What they do not gain is dominated convergence, L²
completeness, or anything requiring the completion. **Their verdict should
stay "unmoved" until the completion lands**, and recording that is more useful
than claiming otherwise.

**For reviewer 08 (probability).** This is the larger unblock, and it is
immediate. A finite index set is an integration space (`crealFinite`), a point
mass is one (`crealDirac`, with `total = 1`), and a detachable subset of a
finite index set is an integrable set. The generic theorems land on
`CReal.sumRange` for free. W1-10 (generalising finite probability) and W2-15
(independence) can now be stated against a carrier that also has a continuous
instance, so the ℚ-only ceiling is gone in principle. What is still missing is
the ℚ↔ℝ bridge: `Rat.expectation` is normalised and `crealFinite`'s integral
is not, so the connection is `expectation = integral / total` and it is stated
here, not proved.

**If the decision had gone the other way (measure-first)** the same two
reviewers would get: a σ-algebra and a measure record, no instances (there is
no non-trivial measurable-set structure to instantiate them at without the
completion), no reuse of the 63 existing `integral.rs` declarations at all,
and the undecidable-membership objection met head-on rather than dissolved.
The measure-first route's first *checkable* deliverable is strictly further
away than the integral-first route's, which landed three instances in a day.

## Consequences

- **Two honest gaps between `IntSpace` and a Petrakis–Zeuner pre-integration
  space.** (i) Their `L` is closed under `|·|` and the lattice operations; the
  record has no `fabs` field. The *obligation* is now dischargeable —
  `IntSpace.CReal.uniformly_continuous_abs` supplies it for the interval
  instance and the finite and Dirac instances have it free — so this is a
  field to add, not a lemma to prove. (ii) Their definition carries two limit
  axioms restricted to set-indexed sequences; ours carries none, because
  `CReal.integral` proves none — they are exactly where the classical strength
  lives, and the graded family handles them. Both gaps make the structure
  *weaker*, so nothing built here is unsound under their definition; both
  should be closed before it is called a pre-integration space without
  qualification.
- The integrable sets of `crealInterval` are trivial (constant indicators),
  by the connectedness argument above. The measure layer's non-trivial content
  today lives on the finite and Dirac instances. This is expected and is the
  reason L¹ is the completion.
- `IntSpace` is a fourth record on the `AlgS`/`Metric` spine. The spine is now
  load-bearing enough that `declare_record`'s `Sort 2` ceiling is a real
  constraint, and it is what forced integrable sets to be curried.
- **Pointfree is the destination, and it is now named.** Coquand and Spitters
  (*Integrals and valuations*, arXiv:0808.1522) prove that integrals on a
  Riesz space and valuations on its spectrum are the same object, via two
  bi-interpretable geometric theories. That is precisely the route ADR-1602
  deferred: **once frames exist, the integral-first development becomes the
  pointfree measure theory for free, in the exact technical sense of that
  paper.** Recording it as the destination — not as work to start — is what
  makes integral-first a strategic choice rather than a local one.

## Alternatives considered

- **Measure-first (σ-algebras, measures, then the Lebesgue integral).**
  Rejected on the reachability measurement above: no instances, no reuse, and
  it meets the undecidability objection instead of dissolving it.
- **Bishop–Cheng integration spaces verbatim.** Rejected on predicativity;
  see the correction above. Cost of not having taken this route: zero.
- **Making `Integrable` a `Prop`.** Impossible without losing the integral —
  `CReal.integral` consumes the modulus.
- **Closure fields on the record** (`Integrable` closed under `+` and scaling).
  Rejected: strictly stronger than any existing theorem proves, and not needed
  once witness independence is derived.
- **Bundling an integrable set as one object.** Blocked: `Sigma`/`Subtype`
  absent (ADR-1595), `declare_record` fixed at `Sort 2`. Currying costs one
  binder.
- **Idempotence (`chi·chi ~ chi`) as the indicator condition.** Rejected: it
  does not give a two-valued function without a decision principle, so it
  claims more than it delivers.

## Related

- [ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) — setoids; and the `Sigma`/`Subtype` absence this ADR ran into again.
- [ADR-1601](adr-1601-classical-logic-enters-as-a-hypothesis-not-as-an-axiom.md) — the hypothesis route, re-measured here at one binder.
- [ADR-1602](adr-1602-the-metric-layer-first-then-pointfree-and-not-open-sets.md) — the metric layer, whose `Metric.Complete` is what L¹ would reuse, and the pointfree deferral this ADR gives a destination.
- [ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md) — the graded family the convergence theorem lands as.
- Petrakis and Zeuner, *Pre-measure spaces and pre-integration spaces in predicative Bishop–Cheng measure theory*, arXiv:2207.08684 — the predicative repair this ADR follows.
- Coquand and Spitters, *Integrals and valuations*, arXiv:0808.1522 — integrals and valuations are the same object; the pointfree destination.
