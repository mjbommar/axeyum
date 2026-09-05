# ADR-1625: L¹ is a metric space from a pointwise distance, and there is no completion functor to reuse

Status: proposed
Date: 2026-09-05
Lane: `l1-completion`
Roadmap: W3-1 follow-on (reviewers 03.4 and 08.5) — closes the gap ADR-1612 named and ADR-1613 unblocked

Index-summary: ADR-1612 said L¹ needed `|·|`-closure on the `IntSpace`
carrier and priced it as record fields; ADR-1613 supplied `Sigma` and made
the bundled carrier legal but left the seminorm blocked on the same lattice
question. **The lattice question was the wrong question.** What the L¹
seminorm needs is not `|·|` and not closure under it, but ONE binary
operation `fdist : carrier → carrier → carrier` behaving like a pointwise
distance, plus four laws that map one-to-one onto four metric laws. Taken as
explicit arguments rather than record fields it needs no change to a
sixteen-field record three instances already fill, it is strictly weaker than
the eight closure fields the obvious design wants, and — the measurement —
**all six analytic obligations of both instances are discharged by existing
lemmas applied verbatim, with zero new estimates**; three of the six are
`Metric.creal`'s own metric laws, so W2-1's `Metric` layer pays for itself a
second time. `IntSpace.crealIntervalL1` and `IntSpace.crealFiniteL1` land as
`Metric`s with `Eq.refl` probes pinning the distance to `CReal.integral |F−G|`
and `CReal.sumRange |f−g|`. The **completion did NOT land**, and the deciding
number is why: of the 33 declarations in `creal/completeness.rs` and
`creal/convergence.rs`, **33 are stated about `CReal` alone and 1 is usable**
— `CReal.limit`, a total `Definition`, which has **zero** algebra lemmas and
**zero** consumers anywhere in the tree. `CReal` is not the completion functor
applied to ℚ and cannot be made one: ℚ is not a `Metric` here at all.

Index-status: proposed

## Context

Two ADRs converge on this file.

**ADR-1612** built `IntSpace`, a sixteen-field constructive integration space,
and recorded the obstruction to L¹ in its own words: an integrable `f` needs an
integrable `|f|`, with `∫|f| ≥ 0` and `|∫f| ≤ ∫|f|`, and the record has no
absolute value on the carrier. It also declined closure fields
(`Integrable f → Integrable g → Integrable (fadd f g)`) as "a stronger axiom
than the existing theorems prove".

**ADR-1613** added `Sigma`, `PSigma` and `Subtype`, which made
`IntSpace.Bundled S := Sigma S.carrier (IntSpace.Integrable S)` a legal
`Metric` carrier and `IntSpace.bundledIntegral` a total function. Its
`intspace/bundled.rs` then declared `IntSpace.bundledDist b₁ b₂ := |∫b₁ − ∫b₂|`
and labelled it, correctly and prominently, **not L¹** — a pseudometric that
does not separate points and is generally smaller than `‖f − g‖₁`. The module
doc closed by naming the remaining piece as the lattice gap.

So the state entering this lane: the carrier exists, the shape of `Metric.dist`
is writable on it, and the actual L¹ seminorm is blocked on a record change
nobody wanted to make.

## Decision

### 1. The L¹ data is a pointwise distance, taken as arguments

`intspace/l1.rs` declares

```text
IntSpace.l1Dist : Π (S : IntSpace)
                    (fdist : S.carrier → S.carrier → S.carrier)
                    (hI : ∀ f g, S.Integrable f → S.Integrable g →
                                 S.Integrable (fdist f g)),
                  S.Bundled → S.Bundled → CReal
  := fun S fdist hI b₁ b₂ =>
       S.integral (fdist (S.bundledFun b₁) (S.bundledFun b₂))
                  (hI _ _ (S.bundledWitness b₁) (S.bundledWitness b₂))
```

and builds the metric from four further hypotheses:

| hypothesis | statement | discharges |
| --- | --- | --- |
| `hAdd` | `∀ f g, Integrable f → Integrable g → Integrable (fadd f g)` | the witness `integralAdd` demands |
| `hNN` | `∀ f g, fle (fconst 0) (fdist f g)` | `Metric.distNonneg` |
| `hSelf` | `∀ f, fle (fdist f f) (fconst 0)` | `Metric.distSelf` |
| `hComm` | `∀ f g, fle (fdist f g) (fdist g f)` | `Metric.distComm` |
| `hTri` | `∀ f g h, fle (fdist f h) (fadd (fdist f g) (fdist g h))` | `Metric.distTriangle` |

Nothing asks that `fdist f g` be `|f − g|`, that the carrier be closed under
`|·|`, or that `fdist` relate to `fadd` and `fscale` at all. **Fusing the
absolute value with the subtraction into one operation is what removes the
lattice question from the statement.** The theorem this file actually proves is
more general than L¹:

> A pointwise distance on the carrier of an integration space, integrated, is a
> metric on the bundles.

ADR-1612's judgement about closure fields stands for closure fields, and the
narrower `hI` this design needs is not one — but note that its stated reason
("a stronger axiom than the existing theorems prove") is no longer accurate for
either shipped instance: `CReal.uniformly_continuous_add` proves `hAdd` for
`crealInterval`, and `IntSpace.Triv.mk` proves it for `crealFinite`.

### 2. The equivalence IS the distance being zero

`Metric` carries its own setoid and then demands
`distSelf : equiv a b → dist a b ~ 0` **and**
`distEquiv : dist a b ~ 0 → equiv a b`. Constructively, "equal almost
everywhere" for L¹ is `∫|f − g| ~ 0` and nothing else, so

```text
IntSpace.L1Equiv S fdist hI b₁ b₂ := CReal.Equiv (IntSpace.l1Dist S fdist hI b₁ b₂) CReal.zero
```

is a *definition*, and both of those fields become `fun a b h => h`. The content
does not vanish; it moves into `equivRefl`, `equivSymm`, `equivTrans` and
`distCongr`, which are proved here from the triangle inequality alone.
`distCongr` is the only one that is not a rearrangement — it is the
quadrilateral estimate run in both directions, factored through
`IntSpace.l1Dist_le_of_equiv` so the second direction is the first applied to
the symmetric hypotheses.

Ten of the twelve `Metric` fields are a theorem of this file **partially
applied**; the binder orders were chosen to make that true.

### 3. It is `IntSpace.bundledL1`, not `Metric.bundledL1`

The brief asked for `Metric.bundledL1`. That name would have been watched by
nothing. `metric/metric_tests.rs` and `intspace/intspace_tests.rs` each assert
that every live declaration in their prelude is on a hand-maintained list, and
each does it with a **name-prefix filter**. A `Metric.*` name declared by the
`IntSpace` prelude falls between them: `metric::`'s kernel never sees it (the
metric prelude does not build `IntSpace`), and `intspace::`'s filter is
`shown.starts_with("IntSpace")`, which does not match it.

This is the same failure mode as the earlier finding that a namespace-prefix
filter is still a literal: six preludes replaced a name list with a prefix and
seven declarations ended up watched by nothing. Declaring inside `IntSpace`
puts the name back under a filter that actually runs — and the filter is what
found the fifteen new names on their first run here, exactly as designed.

`build_intspace_prelude` now calls `build_metric_prelude`. `Metric` does not
depend on `IntSpace`, so there is no cycle; both builders are idempotent.

## The measurement: what the instances cost

`IntSpace.crealIntervalL1 : Π (a b : CReal), CReal.le a b → Metric` and
`IntSpace.crealFiniteL1 : Nat → Metric`. Six analytic obligations, twice:

| obligation | interval witness | finite witness | new estimate? |
| --- | --- | --- | --- |
| `hI` | `IntSpace.CReal.uniformly_continuous_abs` after `CReal.uniformly_continuous_sub` | `IntSpace.Triv.mk` | no |
| `hAdd` | `CReal.uniformly_continuous_add` | `IntSpace.Triv.mk` | no |
| `hNN` | `CReal.abs_nonneg` | `CReal.abs_nonneg` | no |
| `hSelf` | `Metric.CReal.distSelf` | `Metric.CReal.distSelf` | no |
| `hComm` | `Metric.CReal.absSubLe` | `Metric.CReal.absSubLe` | no |
| `hTri` | `Metric.CReal.distTriangle` | `Metric.CReal.distTriangle` | no |

**Zero new estimates.** Three of the six are `Metric.creal`'s own metric laws:
the theorems that made ℝ a metric space are, applied at a point, the theorems
that make L¹ one.

One design choice is load-bearing for that table and worth stating as a rule.
`IntSpace.fsub` was **not** defined as `fadd f (fscale (neg one) g)`, which is
the obvious reading of "difference" in this record. Every `Metric.CReal.*`
lemma is stated about `abs (a + -b)`, and the `fscale` route would have needed a
`mul (neg one) x ~ neg x` bridge, which the ℝ prelude does not have and which
costs a distributivity argument to build. Taking `fdist` as the datum makes all
six witnesses apply with no bridging step. *Match the shape the existing lemma
is stated in, not the shape the record makes available.*

Two `Eq.refl` probes pin the claim rather than the record:

```text
IntSpace.crealIntervalL1_dist : ∀ a b hab F G hF hG,
  Metric.dist (crealIntervalL1 a b hab) (bundle F hF) (bundle G hG)
    = CReal.integral (fun t => CReal.abs (CReal.add (F t) (CReal.neg (G t)))) a b hab …

IntSpace.crealFiniteL1_dist : ∀ m f g,
  Metric.dist (crealFiniteL1 m) (bundle f Triv.mk) (bundle g Triv.mk)
    = CReal.sumRange (fun i => CReal.abs (CReal.add (f i) (CReal.neg (g i)))) (Nat.succ m)
```

Without those, "we built a `Metric`" is a claim about a record. With them it is
a claim about the Riemann integral of `|F − G|` and about `E|X − Y|` on the
finite probability layer (ADR-1616, where the derived measure is counting
measure).

## The deciding number: the completion does not exist to be reused

ADR-1612 measured 0 of 78 when `Sigma` was absent. The question this lane was
sent to answer is what the number is now, with `Sigma`, `Subtype` and
`Metric.Complete` all present. It is worse than it looks, and in an
informative way.

**`CReal.limit` is usable, and unused.** `creal/completeness.rs` declares five
things:

```text
CReal.RegularSeq       : (Nat → CReal) → Prop
CReal.limitSeq         : (Nat → CReal) → Nat → Rat
CReal.limitSeq_regular : ∀ X, RegularSeq X → Regular (limitSeq X)
CReal.limit            : Π (X : Nat → CReal), RegularSeq X → CReal
CReal.limit_dist       : ∀ X h n k, Within (seq (X n) k − seq (limit X h) k) (2/(k+1) + 2/(n+1))
```

`CReal.limit` is a `Definition` producing a `CReal`, and its `RegularSeq`
argument is a `Prop` it only ever *consumes* (it is passed to
`limitSeq_regular` and thence to `CReal.mk`'s own Prop-valued field). So
`CReal.limit X h` **can** appear inside a `Definition` whose result is a
`CReal` — which is precisely what a generic `Metric.completion M`'s `dist`
field would need, since the distance between two Cauchy sequences is a limit of
`CReal`s.

What does not exist is everything you would do with it. There is **no**
`limit_add`, **no** `limit_le`, **no** `limit_nonneg`, **no** `limit_congr` —
no lemma of any kind relating `CReal.limit` to `CReal`'s algebra or order — and
**no consumer of `CReal.limit` anywhere in the crate** outside the two
registries that merely list its name. The development went a different way:
`creal/convergence.rs` carries the algebra of limits (`converges_add`,
`converges_le`, `converges_squeeze`, …) stated about the `Converges`
*predicate*, which never mentions `CReal.limit`, and `CReal.converges_of_cauchy`
hides its limit behind an `Exists` from which no data can be extracted.
`creal.rs`'s own doc says the `RegularSeq`/`limit` route "overshoots
`RegularSeq`'s fixed modulus by a factor of two" and that the development uses
`speedup` instead. `CReal.limit` was superseded and left standing.

**Counting.** `creal/completeness.rs` (5) + `creal/convergence.rs` (28) = 33
declarations. **33 of 33 are stated about `CReal` alone** — every one quantifies
over `f : Nat → CReal` and phrases its bound on the *rational representative
samples* `CReal.seq (f n) n`, a shape that exists only because the elements are
`CReal`s with a canonical sample at their own index. **1 of 33 is reusable for a
generic completion** (`CReal.limit`, and only as a term former). The
genuinely carrier-agnostic file is `creal/speedup.rs`, whose four declarations
are stated about a bare `Nat → Rat` — which is exactly the wrong abstraction for
an arbitrary metric carrier, because there are no rational samples there.

**So the answer to "is `CReal` the completion functor applied to ℚ?" is no, and
not for a fixable reason.** `Metric.dist` is `CReal`-valued, so a `Metric` on ℚ
would have to be `CReal.ofRat`-valued; there is no `Metric.rat` instance in the
library and building one presupposes ℝ. `CReal`'s construction is a hand-built
setoid of regular *rational* sequences, and its regularity condition is stated
in a form (rational samples) that a general metric space cannot express. A
generic `Metric.completion M` would be a *parallel* construction, not a
generalization of this one — the same relationship `metric.rs` already records
between `Metric.Cauchy`/`Complete` and `CReal.Cauchy`/`converges_of_cauchy`
("a parallel restatement, not a generalization", bridged by two named lemmas).

### What a generic completion would actually cost

Stated so the next lane does not re-derive it. The carrier is available:

```text
Metric.CompletionSeq M := Subtype (Nat → M.carrier) (Metric.Regular M)
```

is `Sort 1`, legal as a `Metric` carrier, and `Metric.subspace` already
demonstrates `Subtype` at exactly this universe. `dist` is
`CReal.limit (fun n => M.dist (f n) (g n)) (…)` — total, given a regularity
proof that is itself a closed term. The cost is the four missing lemmas, which
must be proved for `CReal.limit` from `CReal.limit_dist` and nothing else:

1. `limit_congr` — two regular sequences pointwise `Equiv` have `Equiv` limits;
2. `limit_le` / `limit_nonneg` — `le` passes to the limit;
3. `limit_add` — the limit of a sum is the sum of the limits;
4. a speedup bridge, because `n ↦ M.dist (f n) (g n)` is regular at rate
   `2/(m+1) + 2/(n+1)`, twice what `RegularSeq` demands — the same factor-of-two
   overshoot `creal.rs` names, and the reason `speedup` exists.

None is deep; all four are new. That is a bounded, well-specified next task and
it is worth more than L¹ alone, because it makes every `Metric` in the library
completable at once.

## A negative control that had to be moved, and why

The obvious mutation table is the concrete one: offer
`Metric.dist (crealIntervalL1 a b hab) (bundle F hF) (bundle G hG) =
CReal.integral |F − G| …` to the trusted gate with `Eq.refl`, perturb the
integrand, and require a refusal. The **positive** direction of that is fine and
is a shipped declaration (`IntSpace.crealIntervalL1_dist`, admitted during the
prelude build in ordinary time). The **negatives are pathological**: to refuse
`∫F₁ ≡ ∫F₂` the kernel unfolds `CReal.integral`, and the run was still going
after **ten minutes** on three rows. Measured 2026-09-05; the run was killed.

The rule this repository already states — *a pathological negative control is
worth deleting, and a negative control must differ in a SMALL term* — is what
decides it, and the fix is not to weaken the check but to move it to where the
term is small. The mutation table is now stated at a **bound `S` and a bound
`fdist`**, where nothing can unfold and every row settles immediately:

| row | right-hand side | verdict |
| --- | --- | --- |
| `Correct` | `S.integral (fdist f g) (hI f g hf hg)` | **admitted** (the positive twin) |
| `SwappedIntegrand` | `S.integral (fdist g f) …` | refused |
| `DiagonalIntegrand` | `S.integral (fdist f f) …` | refused |
| `SwappedBundles` | correct RHS, bundles swapped on the left | refused |

`SwappedIntegrand` is the sharp one: `fdist g f` is `CReal.Equiv`-equal to
`fdist f g` — that is `IntSpace.l1Dist_comm`, proved in the same file — and
definitionally different, so a probe that accepted it would be measuring
nothing.

The **finite** instance keeps its concrete table (correct bound / short bound /
dropped negation / swapped arguments, with the positive twin), and it is cheap,
because `IntSpace.crealFinite`'s integral is a `Nat.rec` over `CReal.sumRange`
rather than a Riemann sum with a modulus. For the interval instance the
discrimination is done on the **rendered type** instead: the statement must
contain the integrand `fun t => CReal.abs (CReal.add (F t) (CReal.neg (G t)))`
verbatim, in that argument order, which a swap or a dropped negation would not.

General form, worth carrying: **the cost of refusing a definitional equation is
the cost of the reduction the kernel attempts, not the size of the difference
between the two sides.** State the mutation where the heads are opaque.

## Consequences

- `intspace/l1.rs` adds **19 declarations, zero axioms**: two definitions, one
  evaluation probe, four estimates, three setoid laws, two congruence steps,
  `IntSpace.bundledL1` with two `Eq.refl` probes, and the two instances with
  one probe each.
- `build_intspace_prelude` now depends on `build_metric_prelude`. The
  `intspace::` suite pays the metric prelude's build cost.
- The pinned declaration count in
  `intspace/intspace_tests.rs::every_intspace_declaration_is_present_and_derived`
  moved. It was **recounted from the test's own output**, not incremented.
- `IntSpace.bundledDist` (ADR-1613) is now superseded for every purpose except
  its original one — demonstrating that a `Metric.dist`-shaped function was
  writable. It is left in place; its module doc already says it is not L¹.
- **L¹ is a metric space and is NOT yet known to be complete.** Nothing here
  claims completeness, and `Metric.Complete (crealIntervalL1 a b hab)` is not
  declared. Petrakis–Zeuner's L¹ is the *completion* of the pre-integration
  space; what landed is the pre-integration space's metric, which is the object
  that gets completed.

## Alternatives rejected

**Eight new record fields** (`fabs`, `absIntegrable`, `addIntegrable`,
`scaleIntegrable`, and four lattice laws), taking `IntSpace` from sixteen fields
to twenty-four. Rejected: it is a strictly stronger assumption than the metric
needs, it forces twenty-four new proof obligations across three instances
(`instances.rs` twice and `detachable.rs` once) for content the seven arguments
supply, and it rewrites `interval_args` — the vector the field-mutation test
rebuilds with one slot replaced. The hypothesis form gives the same theorem and
leaves the record alone. If a later lane finds three or more instances all
supplying the same witnesses, promoting them to fields is a mechanical change
that this file's proofs survive unchanged.

**`fsub` via `fscale (neg one)`.** Rejected on the measurement above: it costs a
bridge lemma the ℝ prelude does not have, and buys nothing the metric needs.

**Building `Metric.completion` first and L¹ second.** Tempting — a generic
completion is worth more — but it would have landed nothing checkable in this
lane, and the reuse number that decides its priority is only credible once
someone has looked at what `CReal.limit` actually is. It is now specified above
as a bounded task.
