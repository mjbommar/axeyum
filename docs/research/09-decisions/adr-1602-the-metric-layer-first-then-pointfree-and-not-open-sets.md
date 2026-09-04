# ADR-1602: topology is built metric-first, then pointfree; open-set topological spaces are not adopted

Status: proposed
Date: 2026-09-04
Lane: `topology-decision`
Roadmap: W0-3 (the constructive-topology design ADR) and W2-1 (the metric-space carrier) — reviewers 06.1, 06.2, and, downstream, 03 / 05 / 08

Index-summary: reviewer 06 is the emptiest shelf in the library (zero
topology declarations) and asked which constructive topology to adopt — open
sets, apartness spaces, or locales. The question was decided the way ADR-1595
decided quotients: by **building the thing that was supposed to depend on the
answer** and measuring what it actually needed. W2-1's metric-space carrier
landed — a twelve-field setoid-flavored record, two instances (ℝ under
`|x−y|`, the Euclidean plane under `sqrt (CPoint.distSq P Q)`), **49
declarations** in a new `Metric` namespace, every one with an empty
`Kernel::axiom_footprint`, 17 tests in 64 s — **and it needed no topology at all**. `Metric.Complete` is stated for
an arbitrary metric space and `Metric.creal_complete` proves ℝ satisfies it;
the entire cost of generalizing `CReal.converges_of_cauchy` off ℝ was two
already-landed bridge lemmas and three `Exists.rec`s. So the roadmap's
`W2-1 → W0-3` dependency is **measured false** and should be deleted, and the
three-way question is not a choice but an order. **Recommendation: build the
metric/uniform layer first (it carries W2-2, W2-3 and W2-10 on its own);
adopt POINTFREE (frames/locales) for topology proper when a
non-metrizable space is actually needed; do NOT adopt open-set topological
spaces.** Apartness is not a third option — it is what a metric already
supplies (`d(x,y) > 0`), and `CReal` has the full apartness apparatus
already.
Index-status: proposed

## Context

Reviewer [06 — Topology](../../math-department/06-topology.md) is the
shortest review in the department and the one that blocks the most people.
Measured 2026-09-04 at `1856cdb3c`: `topology`, `open_set`, `compact_space`,
`metric_space`, `connected`, `homotopy`, `homology` and `fundamental_group`
each returned **zero** files under `crates/axeyum-lean-kernel/src/`, against a
positive control (`riemann`) of 16. Three other reviewers — 03 classical
analysis, 05 geometry, 08 probability — are recorded as blocked behind it.

The reviewer's own framing, and the roadmap's:

> point-set topology is awkward constructively. Open sets defined by
> membership predicates behave badly without excluded middle, and the
> constructive tradition prefers *located* subsets, *apartness spaces*, or
> formal/pointfree topology (locales) precisely because the classical
> definitions do not transfer. So the right first move here is a design
> decision, not a transcription of a textbook chapter.

The roadmap encodes that as W0-3 ("Constructive topology design ADR: open
sets, apartness spaces, or locales — determines whether the analysis shelf
ever generalizes") with **W2-1 and W2-2 depending on it**.

[ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md),
landed the same day, settled a structurally identical question — three
reviewers asking for `Quot.sound` — not by weighing arguments but by building
the first isomorphism theorem over `AlgS.Group` by the setoid route and
counting what it cost. This ADR uses the same method on the same day for the
same reason: the arguments on all three sides of W0-3 are correct as far as
they go, and none of them predicts a number.

## The measurement

### What was built

`crates/axeyum-lean-kernel/src/metric.rs`, commits `e43a8105c` (the record,
the ℝ instance, the generic theorems, completeness) and `b34e2dbd7` (the
Euclidean plane). Forty-nine declarations in a new `Metric.*` namespace, all admitted by
`Kernel::add_declaration` and all listed by
`shape_search --include-constructed --ns Metric` (`verdict: FOUND 49`).

`Metric` is a twelve-field `Sort 2` record built with the **`AlgS` spine's own
`declare_record`** (`nat_prelude::structures`, ADR-1588's machinery), because
`CReal`'s equality is the defined relation `CReal.Equiv` and not the kernel's
primitive `Eq` (ADR-0512):

| # | field | type |
|---|---|---|
| 0 | `carrier` | `Sort 1` |
| 1 | `equiv` | `carrier → carrier → Prop` |
| 2–4 | `equivRefl` / `equivSymm` / `equivTrans` | the setoid laws |
| 5 | `dist` | `carrier → carrier → CReal` |
| 6 | `distCongr` | `equiv a a' → equiv b b' → Equiv (dist a b) (dist a' b')` |
| 7 | `distNonneg` | `le zero (dist a b)` |
| 8 | `distSelf` | `equiv a b → Equiv (dist a b) zero` |
| 9 | `distEquiv` | `Equiv (dist a b) zero → equiv a b` |
| 10 | `distComm` | `Equiv (dist a b) (dist b a)` |
| 11 | `distTriangle` | `le (dist a c) (add (dist a b) (dist b c))` |

Bishop's axioms (*Constructive Analysis*, §4.1) verbatim, with the identity of
indiscernibles as **two separate one-directional fields** rather than one
`Iff` — see §"What the build taught" below for why that is not cosmetic.

Two instances:

- **`Metric.creal`** — ℝ under `d(x,y) = |x − y|`, i.e.
  `fun x y => CReal.abs (CReal.add x (CReal.neg y))`.
- **`Metric.cpoint`** — the Euclidean plane under
  `d(P,Q) = CReal.sqrt (CPoint.distSq P Q)`.

And the theorem the carrier exists to make possible, read from the kernel:

```text
Metric.Complete       : (M : Metric) -> Prop
Metric.creal_complete : Metric.Complete Metric.creal
```

with `Complete M := ∀ f, Metric.Cauchy M f → ∃ L, Metric.TendsTo M f L`.

Two more statements that are true of **every** metric space rather than of one
carrier, which is the whole point of having a carrier:

```text
Metric.dist_self : (M : Metric) -> (a : Metric.carrier M) ->
                   CReal.Equiv (Metric.dist M a a) CReal.zero
Metric.dist_quadrilateral :
  (M : Metric) -> (a b c e : Metric.carrier M) ->
  CReal.le (Metric.dist M a e)
           (CReal.add (Metric.dist M a b)
                      (CReal.add (Metric.dist M b c) (Metric.dist M c e)))
```

### 1. Did it land? Yes, and with no topology.

Every one of the 49 declarations has an **empty axiom footprint**, read from
`Kernel::axiom_footprint` and not from a rendered name, by a test that derives
its name list from the prelude handle and the `RecordNames` selectors rather
than from a literal:

```
running 17 tests
test metric::metric_tests::every_metric_declaration_is_axiom_free ... ok
test metric::metric_tests::every_metric_declaration_is_present_and_derived ... ok
test metric::metric_tests::metric_prelude_builds ... ok
... 14 more
test result: ok. 17 passed; 0 failed; finished in 64.41s
```

(`--release`, `--test-threads=4`; `RUST_MIN_STACK` is not needed in release.)

**Nothing in the record is a subset.** There is no membership predicate, no
family of opens, no union, no index type. The reviewer's constructive
objection — "open sets defined by membership predicates behave badly without
excluded middle" — never came up, because a metric space is a *structure over
a carrier*, exactly what the `AlgS` spine already builds nine of.

### 2. What the generalization actually cost

This is the number W0-3 was supposed to be about. The roadmap's claim is that
the topology decision "determines whether the analysis shelf ever
generalizes". Here is the generalization, and what it cost.

`CReal.converges_of_cauchy` proves completeness for ℝ specifically. It is
phrased on the rational **samples** of the Cauchy representation:

```text
CReal.Converges f L := ∃ K, ∀ n, Within (seq (f n) n − seq L n) (natDivSucc K n)
CReal.Cauchy f      := ∃ K, ∀ m n, Within (seq (f m) m − seq (f n) n) (…)
```

`Metric.Cauchy`/`Metric.TendsTo` are phrased on `M.dist`. Crossing that gap
is the entire content of `Metric.creal_complete`, and **both bridges already
existed**:

| step | lemma | already in tree |
|---|---|---|
| metric hypothesis → `CReal.Cauchy f` | `CReal.cauchy_of_abs_diff_le` | yes (`creal/ivt.rs`) |
| `CReal.Cauchy f` → `∃ L, Converges f L` | `CReal.converges_of_cauchy` | yes, used as a black box |
| `Converges f L` → metric conclusion | `CReal.close_within_of_within` | yes (`creal/uniform_convergence.rs`) |

Everything else is three `Exists.rec` eliminations and one arithmetic
witness (`rate := 1 + (K' + 1)`, the numerator
`close_within_of_within` hands back). All three elimination targets are
`Prop`, so `Exists`'s `Prop`-only elimination — the obstruction ADR-1595
measured for `Type`-valued constructions — is never in the way here.

**The obstruction to generalizing analysis off ℝ was never the absence of a
topology. It was that `Converges`/`Cauchy` are stated one level down, on
rational samples.** Two lemmas that were written for the IVT and the
Weierstrass M-test, for unrelated reasons, are exactly what closes it. No
choice among open sets, apartness and locales would have made this easier or
harder by a single step.

### 3. Cost, counted

| measure | value |
|---|---|
| Rust added (`metric.rs`, term-building + docs) | 2,729 lines |
| Rust added (`metric/metric_tests.rs`) | 743 lines |
| declarations added | **49** — 1 inductive, 1 constructor, 1 recursor, 20 definitions (12 of them the record's selectors), 26 theorems |
| `shape_search --include-constructed` total | 3,611 (the `metric` group is 49 of them; before this lane the example did not index the group at all) |
| `metric::` suite wall clock | **64.41 s**, 17 passed (`--release`, `--test-threads=4`) |
| axioms in the footprint of any of the 37 | **0** |
| `Subtype` / `Sigma` in the kernel | **absent** (positive control: `Exists` present, 22 hits in `prelude.rs`) |

Lemmas that had to be built because the reals prelude does not have them —
each one a *real* gap, not a stylistic preference:

| built here | why the prelude did not have it |
|---|---|
| `Metric.CReal.negZero` | there is no `CReal.neg_zero` |
| `Metric.CReal.absZero` | there is no `CReal.abs_zero` |
| `Metric.CReal.leOfSubNonpos` | there is no "move a term across `le`" lemma |
| `Metric.CReal.absSubLe` | there is no `CReal.abs_neg` or `abs_sub_comm` |
| `Metric.CReal.subTelescope` | the telescoping identity `(a−b)+(b−c) ~ a−c` had no name |
| `Metric.CPoint.equivRefl/Symm/Trans` | the plane prelude builds reflexivity **inline** and never needed the other two |
| `Metric.CPoint.subTelescope` | `point_sub_telescope_fact` is a private Rust helper with no declaration |
| `Metric.CPoint.dotLeSqrtMul` | **unsquared Cauchy–Schwarz** — see below |

### 4. The plane instance is where the vocabulary question was actually decided

`CPoint.distSq` is the **squared** distance, and it is not a metric:
`d(0,2)² = 4 > 1 + 1 = d(0,1)² + d(1,2)²`. That is not an argument in this
ADR, it is a test:
`metric_tests::the_planes_squared_distance_is_refused_as_the_dist_field`
substitutes `CPoint.distSq` for `Metric.CPoint.dist` in the plane instance,
leaves the other eleven arguments untouched, and requires
`Kernel::add_declaration` to refuse. It does. So the square root is a measured
requirement.

Taking the root means the triangle inequality has to be proved **unsquared**,
and neither of the plane prelude's existing bounds gives it:
`CPoint.dist_sq_triangle_sq_bound` is squared (Lagrange-derived) and
`CPoint.dist_sq_double_sum_bound` carries a factor of 2. The gap was exactly
one lemma:

```text
Metric.CPoint.dotLeSqrtMul :
  (U V : CPoint) -> CReal.le (CPoint.dot U V)
                             (CReal.sqrt (CReal.mul (dot U U) (dot V V)))
```

`CPoint.cauchy_schwarz` is squared; carrying it under `CReal.sqrt_le_sqrt`
needs `sqrt (t·t) ~ |t|`, which is `sqrt_sq` at `|t|` composed with
`CReal.mul_self_abs`. `sqrt_sq` alone will not do it — it needs `0 ≤ t`, and
the cross term `⟨U,V⟩` has no known sign, and `CReal` has no `le_or_lt`. This
is the same obstruction `Complex.abs_add_le` hit and the same fact that
resolved it (`ComplexPrelude::norm_sq_add_le`'s doc records the refuted
attempts in detail).

**A stale blocker, corrected.** `CPointPrelude::cauchy_schwarz`'s doc comment
says the unsquared norm form "is not expressible, let alone provable, here"
because "this kernel has `CReal.natSqrt` but no `CReal.sqrt`". That was true
when it was written. `CReal.sqrt`, `sqrt_sq`, `mul_self_sqrt`, `sqrt_mul` and
`le_of_sq_le` landed afterwards. `Metric.CPoint.distTriangle` — Euclid I.20 on
the unsquared distance — is the counterexample, and it landed on the first
kernel run. This is the third instance this quarter of an in-tree blocker
outliving its cause; verify a named blocker before treating it as one.

### 5. Two methodological findings, both from failing controls

**A concrete-numeral reduction probe on `CReal` is vacuous.** The first
version of the "does `Metric.dist Metric.creal` reduce to `|x − y|`?" probe
used `CReal.one` and `CReal.zero`, with a negative control asserting the same
`Equiv.refl` must NOT prove the swapped statement `|1−0| ~ |0−1|`. **The
negative control failed**: `CReal.zero` and `CReal.one` are closed terms that
compute, so both sides whnf to the same rational and `Equiv.refl` proves it.
A numeral probe cannot distinguish "the selector reduced" from "both sides
happened to evaluate alike". Both probes (and both plane probes) now use
symbolic arguments, where the two terms are stuck and genuinely different.

**The two directions of the identity of indiscernibles are different
theorems, and the record has to keep them apart.** On ℝ, `distSelf`
(`a ~ b → |a−b| ~ 0`) is three steps; `distEquiv` (`|a−b| ~ 0 → a ~ b`) needs
the *order* — `le_abs_self`, `neg_le_abs`, `equiv_of_le_le`, and a
move-across-`le` lemma that had to be built. `metric_tests::
the_two_identity_directions_are_not_interchangeable` puts each in the other's
slot and requires a refusal. Classically this is one biconditional; here it is
two fields with different proofs and different costs. Any future carrier
(uniform space, apartness space, locale) has to keep that split.

## Decision

**Adopt a metric/uniform layer as the library's topology for the foreseeable
work, and pointfree (frames / locales) for topology proper when a genuinely
non-metrizable space is needed. Do not adopt open-set topological spaces.
Delete the `W2-1 → W0-3` dependency: it is measured false.**

In order:

1. **The metric layer is the load-bearing one and it exists now.** W2-2
   (continuity), W2-3 (Bishop compactness and the EVT), W2-10 (products and
   subspaces) are all reachable from `Metric` with no further design decision.
   Bishop compactness *is* total boundedness plus completeness — a metric
   notion, with `Metric.Complete` already landed — so the one compactness the
   roadmap actually wants is downstream of W2-1, not of W0-3.
2. **Apartness is not a third option; it is what the metric layer already
   supplies.** On a metric space, `Apart x y := lt zero (dist x y)`, and
   `CReal` already carries the whole constructive apparatus: `CReal.Apart`,
   `apart_symm`, `apart_irrefl`, `apart_congr`, `not_equiv_of_apart` (one-way
   on purpose — the converse is Markov's principle) and `lt_cotrans`
   (Bishop's cotransitivity). An apartness-space carrier is a *weakening* of
   `Metric` — drop `dist` and keep the relation — and should be built, if at
   all, by projecting out of `Metric`, the way `AlgS.Group.ofAlg` projects
   (ADR-1592). It is not a competing foundation.
3. **Topology proper, when it is needed, is a frame.** A frame is an algebraic
   structure — a complete lattice with one distributivity law — and this lane
   just demonstrated that `declare_record` builds an arbitrary
   setoid-flavored structure at zero design cost (twelve fields; the only work
   was the field-shape closures). A *family of open subsets*, by contrast, needs
   closure under **arbitrary** unions, which means quantifying over an index
   type: `(I : Sort 1) → (I → carrier → Prop) → …`. That pushes the record's
   universe up, and arbitrary union is precisely where constructive trouble
   concentrates (membership in a union is not decidable). The record machinery
   is shaped for the algebra and against the subsets.
4. **Do not build open-set topological spaces at all**, not even as a
   "standard" carrier for interoperability. Nothing in the roadmap needs
   them, they are the option the constructive tradition specifically warns
   against, and a carrier nobody instantiates is a maintenance cost with no
   theorem behind it.

### The one thing that is genuinely blocked

**Subspaces need a `Subtype`, and this kernel has none.** Verified here
(case-sensitive search across `crates/axeyum-lean-kernel/src/`, positive
control `Exists`): no `Subtype`, no `Sigma`; the case-insensitive `sigma` hits
are the divisor-sum function. ADR-1595 reached the same conclusion from the
other side (the image of a group homomorphism).

The workaround this lane recommends, by analogy with the two things that
already work this way: **relativize, do not carve.** `AlgS.Hom.ker` and
`AlgS.Hom.image` are *predicates* on the ambient carrier, not new types; and
ADR-1595's quotient group is the same carrier under a coarser equivalence.
A subspace of a metric space should likewise be a predicate `P : carrier →
Prop` plus statements relativized to it (`Metric.CompleteOn M P`,
`Metric.TotallyBoundedOn M P`), not a new `Metric` over a carved carrier. The
`CReal` development already does exactly this — `UniformlyContinuousOn`,
`supOn`, `HasDerivativeOn` are all interval-relativized rather than
subtype-carved — so this is the established idiom, not a new one.

## What changes downstream

| item | before | after |
|---|---|---|
| **W0-3** | open decision, blocking W2-1 and W2-2 | **closed by this ADR** |
| **W2-1** | not started, depends on W0-3 | **landed** (`e43a8105c`, `b34e2dbd7`); the W0-3 dependency was false |
| **W2-2** — continuity as a topological notion; `UniformlyContinuousOn` implies it | depends on W0-3, W2-1 | depends on **W2-1 only**. Restate as: `Metric.UniformlyContinuous M N f` with an explicit modulus, `Metric.Continuous` pointwise, then `CReal.UniformlyContinuousOn F a b → Metric.UniformlyContinuous` relativized to the interval predicate. No opens. |
| **W2-3** — Bishop compactness on intervals, EVT as an instance | depends on W2-1 | unchanged, and now unblocked. `Metric.Complete` exists; `Metric.TotallyBounded` is the remaining definition. |
| **W2-10** — products and subspaces | depends on W2-1 | **split.** The *product* is buildable today (`CReal.max` or `CReal.add` on the two distances; both exist, and the triangle inequality follows from `max_le`/`add_le_add`). The *subspace* is blocked on `Subtype` and should be relativized instead — see above. Do not size these as one task. |
| **W2-21** — a topological-space carrier, ℝ as the first instance | depends on W0-3 | build it as a **frame** (`Top.Frame`), ℝ's opens generated by rational intervals, via `declare_record`. **Not on the critical path** for W2-2, W2-3 or W3-1. |
| **W3-1** — measure and the Lebesgue integral | depends on W0-2, W0-3, W2-1 | the W0-3 dependency needs re-examination and this ADR does **not** settle it. The constructive route (Bishop; Coquand–Spitters) is *integration first* — a Daniell/Riesz functional on a lattice of simple functions — which needs no opens; but this lane did not build any of it and states that as a lead, not a result. |
| **reviewer 06 topology** | "nothing to review", zero declarations | 49 declarations; its Next-Five items 1 (the decision) and 2 (the metric carrier with ℝ and `CPoint`, completeness lifted) are done. Items 3–5 are ordinary work with no decision in front of them. |
| **reviewer 03 classical analysis** | "unmoved; needs W0-2, W0-3, W3-1" | the "blocked behind topology" claim is **weakened**, not cleared: completeness and the metric vocabulary now exist, and measure's dependence on opens is a lead rather than a fact. |
| **reviewer 08 probability** | blocked behind measure behind topology | same, one level further out. |
| **reviewer 05 geometry** | the differential half blocked behind topology | manifolds still need a genuine topological carrier (W2-21); this ADR says build it as a frame, and says it is not urgent. |

## Consequences

- The library gains a topology shelf that is 49 declarations deep instead of
  zero, and the first two theorems in it that hold of every instance rather
  than of one carrier.
- The three-way question W0-3 posed is answered by *not choosing*: the metric
  layer is not one of the three options and it is what the analysis shelf
  actually needed.
- A roadmap dependency was refuted by building the dependent item. This is the
  second such refutation in two days (ADR-1595 refuted the claim that the
  quotient shelf needed `Quot.sound`) and the pattern is worth naming: **a
  "blocked on X" in a roadmap is a claim about one route, and this repository's
  are reliably pessimistic.**
- **Revisit this ADR** if a measured theorem is shown to be unreachable
  through the metric layer — the honest trigger is a *specific statement* that
  a frame or an apartness space would deliver and `Metric` cannot, not a
  general preference for more vocabulary.

## Alternatives considered

- **Open-set topological spaces.** Rejected on two grounds, one constructive
  (arbitrary unions and undecidable membership, which is the reviewer's own
  objection) and one measured (the record machinery is shaped for algebra;
  arbitrary-index closure raises the universe and buys nothing the metric
  layer does not already supply).
- **Apartness spaces as the primary carrier.** Not rejected — subsumed. A
  metric supplies an apartness; ℝ already has the full apparatus. Build an
  apartness carrier by projection when a non-metric example appears.
- **Locales first, before the metric layer.** Rejected on ordering, not on
  merit: W2-2, W2-3 and W2-10 do not need it, and a carrier with no instance
  and no theorem is a cost with no return. The decision is *when*, not
  *whether*.
- **Deferring W0-3 until a topological theorem forces it.** This is close to
  what the ADR recommends, but leaving the question formally open kept three
  reviewers and five roadmap items marked as blocked on it. Closing it with an
  order — metric now, pointfree later, open sets never — is what unblocks them.

## Related

- [ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) —
  the sibling decision, same method, same day; also the source of the
  `Subtype`/`Sigma` absence finding.
- [ADR-1588](adr-1588-a-setoid-flavored-alg-spine-for-creal.md) — the `AlgS`
  spine whose `declare_record` machinery `Metric` reuses unchanged.
- [ADR-0512](adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md) — why `CReal`'s equality is
  `CReal.Equiv` and not `Eq`, which is why `Metric` carries an `equiv` field.
- [06-topology.md](../../math-department/06-topology.md) — the review this
  answers.
- [00-roadmap.md](../../math-department/00-roadmap.md) — W0-3, W2-1, W2-2,
  W2-3, W2-10, W2-21, W3-1.
