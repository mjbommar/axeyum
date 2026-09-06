# ADR-1678: The metric completion was priced against the wrong term former, and the carrier predicate already exists

Status: proposed
Date: 2026-09-06
Lane: `metric-completion`
Roadmap: W2-1 follow-on — the completion [ADR-1625](adr-1625-l1-is-a-metric-space-from-a-pointwise-distance-and-the-completion-functor-does-not-exist-yet.md) specified and did not build

Index-summary: ADR-1625 sized a generic `Metric` completion at "four new
lemmas about `CReal.limit`, proved from `CReal.limit_dist` and nothing else",
over a carrier `Subtype (Nat -> M.carrier) (Metric.Regular M)`. Both halves are
re-measured here and both move. **`Metric.Regular` does not exist** — all eight
`Regular` tokens in `metric.rs` are `ReducibilityHint::Regular(1)` — but it
does not need to: `Metric.CauchyAt M f 1` unfolds to exactly the regularity
condition, so the carrier predicate costs zero new estimates. **The four lemmas
are not on the critical path at all**, because `CReal.limit` is the *superseded*
term former (`creal.rs` says so in its own words) and the live route
`CReal.mk (speedup (diagonal D) K) (regular_of_scaled_cauchy ...)` already has
all three of its bridges shipped: `CReal.scaledCauchy_of_abs_diff_le`,
`CReal.regular_of_scaled_cauchy`, `CReal.converges_of_scaled_cauchy` — the last
of which **names** the limit, so `limit_congr`/`limit_le`/`limit_add`/
`limit_nonneg` are `converges_unique`/`converges_le`/`converges_add`/
`converges_lower_bound` applied verbatim. ADR-1625's "1 of 33 reusable" rests on
an inverted inference: `Metric.dist` is `CReal`-valued, so the completion's
distance is the limit of a `Nat -> CReal` sequence and "stated about `CReal`
alone" is the *precondition* for applicability, not a disqualification. Its
`33` itself IS re-derivable, by a method it did not state (live
`add_declaration` sites outside `#[cfg(test)]` modules: the naive count is 36,
and the three extras are `converges_le_tests`'s own mutation probes). The one
genuinely new piece of mathematics is a single metric-level estimate.

Index-status: proposed

## Context

`Metric.Complete` has two witnesses in the tree — `Metric.creal_complete`
(`metric.rs`) and `Metric.prod_complete` (`metric_prod.rs`) — plus
`Metric.creal_completeOn_interval`, which is a witness of the *different*
predicate `Metric.CompleteOn` (`metric/compactness.rs`), not of
`Metric.Complete`. This is a small correction to the count the lane brief
carried (three witnesses of `Metric.Complete`): two, plus one of a relative
predicate that `Metric.Compact` consumes via `And (TotallyBounded M)
(Complete M)`.

ℝⁿ (`RN.metric : Nat -> Metric`, `rn.rs`) is not proved complete; L¹
(`IntSpace.crealIntervalL1`, `IntSpace.crealFiniteL1`, ADR-1625) is not proved
complete and has no completion; and the Euclidean plane cannot inherit the
product's, because `Metric.cpoint_of_prod` / `Metric.prod_of_cpoint` relate
`Metric.cpoint` to `Metric.prod Metric.creal Metric.creal` by a carrier
equivalence, not an isometry.

ADR-1625 closed by specifying the completion as "a bounded, well-specified next
task" worth more than L¹ alone. This ADR is the re-measurement that task was
supposed to start from. **It re-measures rather than inherits**, because the
specification carries a name that does not exist and a reuse count nobody has
re-derived.

## The four measurements

### 1. `Metric.Regular` does not exist, and is not needed

ADR-1625 writes the carrier as
`Metric.CompletionSeq M := Subtype (Nat -> M.carrier) (Metric.Regular M)`.

```
grep -rn 'name_str([^)]*"Regular' metric.rs metric/ metric_prod.rs   -> no hits (exit 1)
grep -rn 'name_str([^)]*"Regular' src/                               -> CReal.Regular, CReal.RegularSeq
```

The negative and its positive control are the same pattern in one method; the
control fires twice, so the empty metric-tree result is a real absence and not a
broken pattern. Every `Regular` token in `metric.rs` (8), `metric/continuity.rs`
(11), `metric/subspace.rs` (2), `metric/compactness.rs` (1), `metric_prod.rs`
(1) and `metric/metric_tests.rs` (7) is `ReducibilityHint::Regular(1)`.

It does not need to exist as new content. `metric.rs::declare_cauchy_at` builds

```text
Metric.CauchyAt M f K := forall m n,
  CReal.le (M.dist (f m) (f n))
           (CReal.ofRat (Rat.add (Rat.natDivSucc K m) (Rat.natDivSucc K n)))
```

(the bound is `pair_rate_at`), so `Metric.CauchyAt M f 1` is literally
`d(f m, f n) <= 1/(m+1) + 1/(n+1)` — Bishop's regularity condition, at the
fixed modulus, already a shipped `Definition` with
`ReducibilityHint::Regular(1)`. **The carrier predicate costs zero new
estimates.** Naming it `Metric.RegularSeq M := fun f => Metric.CauchyAt M f 1`
is a readability `Definition` whose evaluation test is a reduction probe, not a
proof.

The modulus has to be *fixed* in the carrier, not existentially quantified:
`Metric.Cauchy M f := exists K, Metric.CauchyAt M f K` is a `Prop`,
`Exists.rec` is `Prop`-only, and the completion's `dist` field must produce a
`CReal`. This is the same kernel fact `CReal.scaledCauchy_of_abs_diff_le`'s own
doc comment cites as the reason that lemma exists separately from
`CReal.cauchy_of_abs_diff_le`.

### 2. ADR-1625's `33` is re-derivable; the method is what was missing

Reviewer 02 could not re-derive it. The naive count is 36:

| file | `add_declaration` sites | live |
| --- | --- | --- |
| `creal/completeness.rs` | 5 | 5 |
| `creal/convergence.rs` | 31 | 28 |
| **total** | **36** | **33** |

The three non-live sites are inside `#[cfg(test)] mod converges_le_tests`
(`convergence.rs:3311-`): `__convergesLeConcreteOk`, `__convergesLeConcreteBad`,
`__convergesLeVacuous` — that module's own mutation probes, offered to the
kernel and never shipped. **Method, stated so the next lane does not re-derive
it: live declarations are `add_declaration` sites outside `#[cfg(test)]`
modules, counted by brace-matching the attribute's module, not by grep.** With
that method ADR-1625's `5 + 28 = 33` is exact, and its `28` for
`creal/convergence.rs` is exact.

### 3. "1 of 33 reusable" rests on an inverted inference

ADR-1625's argument is: all 33 "quantify over `f : Nat -> CReal` and phrase
their bound on the rational representative samples", therefore only
`CReal.limit` (as a term former) survives for a generic completion.

The premise is right and the conclusion does not follow. `Metric.dist` is
**`CReal`-valued**. The object whose limit defines the completion's distance is

```text
D : Nat -> CReal,   D n := M.dist (f n) (g n)
```

which is a `Nat -> CReal` sequence for a completely arbitrary `Metric M`. Being
stated about `Nat -> CReal` is therefore the *precondition* for applying a
theorem to `D`, not a disqualification. Under the criterion **"instantiates at
`D` for a generic `M`"**, all 33 apply. Under the narrower criterion
**"consumed by the construction below"**, the set is:

`CReal.Converges`, `CReal.Cauchy`, `CReal.regular_of_scaled_cauchy`,
`CReal.converges_of_scaled_cauchy`, `CReal.converges_unique`,
`CReal.converges_add`, `CReal.converges_le`, `CReal.converges_of_const`,
`CReal.converges_of_equiv`, `CReal.converges_of_close`,
`CReal.converges_lower_bound`, `CReal.converges_upper_bound`,
`CReal.converges_cauchy`, `CReal.converges_of_cauchy` — **14 of 33**, none of
which is `CReal.limit`.

Both numbers are reported because neither alone is honest: 33/33 measures
applicability and overstates use; 14/33 measures use and depends on the route
this ADR chooses. What is *not* defensible is 1/33, whichever criterion is
applied — `CReal.limit` is the one declaration on the list the construction
below never touches.

### 4. The sizing priced the wrong term former

ADR-1625 sizes the completion at four new lemmas — `limit_congr`, `limit_le`/
`limit_nonneg`, `limit_add`, and a speedup bridge — "which must be proved for
`CReal.limit` from `CReal.limit_dist` and nothing else".

`CReal.limit` is the superseded route. `creal.rs`'s own doc says the
`RegularSeq`/`limit` construction "overshoots `RegularSeq`'s fixed modulus by a
factor of two" and that the development uses `speedup` instead; ADR-1625 itself
records that `CReal.limit` has no consumers anywhere in the crate. The live
route for turning a real-valued Cauchy estimate into an actual `CReal` is the
one `CReal.sup_on`, `CReal.integral` and `CReal.ivt_exact_root` all take, and
its three bridges are **already shipped**:

| shipped bridge | does |
| --- | --- |
| `CReal.scaledCauchy_of_abs_diff_le` | real-valued estimate `\|f m - f n\| <= K/(m+1) + K/(n+1)` -> the `(K, per-pair)` `Within` bound as **data** (it exists precisely because `Exists.rec` cannot give it back) |
| `CReal.regular_of_scaled_cauchy` | that data -> `Regular (speedup (diagonal f) K)`, i.e. `CReal.mk`'s own field |
| `CReal.converges_of_scaled_cauchy` | **names** the limit: `Converges f (CReal.mk (speedup (diagonal f) K) (regular_of_scaled_cauchy f K h))` |

The third is the one that dissolves the sizing. With `Converges D L` in hand for
a *named* `L`, ADR-1625's four lemmas are corollaries of shipped theorems:

| ADR-1625 lemma | is | new work |
| --- | --- | --- |
| `limit_congr` | `converges_of_equiv`/`converges_of_close` + `converges_unique` | none |
| `limit_le` | `converges_le` — already `Converges f L -> Converges g M -> (forall n, le (f n) (g n)) -> le L M` | none |
| `limit_nonneg` | `converges_lower_bound` against `converges_of_const zero` | none |
| `limit_add` | `converges_add` + `converges_unique` | none |
| speedup bridge | `regular_of_scaled_cauchy` — shipped, and exact (`Rat.natDivSucc_scale`, no widening) | none |

**Zero of the five is new.** The factor-of-two overshoot ADR-1625 budgets for is
absorbed by `scaledCauchy_of_abs_diff_le`'s `K |-> K + 2`, which is already paid.

## Decision: the route, and what it actually costs

### The construction

```text
Metric.RegularSeq M f       := Metric.CauchyAt M f 1                    (Definition, 0 estimates)
Metric.CompletionSeq M      := Subtype (Nat -> M.carrier) (Metric.RegularSeq M)  (Sort 1, ADR-1613)
Metric.completionDistSeq M x y : Nat -> CReal
                            := fun n => M.dist (Subtype.val x n) (Subtype.val y n)
Metric.completionDist M x y := CReal.mk (CReal.speedup (diagonal ...) K)
                                        (CReal.regular_of_scaled_cauchy ...)
Metric.completionEquiv M x y := CReal.Equiv (Metric.completionDist M x y) CReal.zero
Metric.completion M : Metric
```

Taking `equiv` to be "the distance is zero" is ADR-1625 section 2's own trick
from L¹, and it has the same consequence here: `distSelf` and `distEquiv`
become `fun a b h => h`, and the content moves into `equivRefl`/`equivSymm`/
`equivTrans`/`distCongr`, all of which are limit algebra over `Converges`.

### The one genuinely new estimate

Feeding `scaledCauchy_of_abs_diff_le` needs, at the *metric* level,

```text
Metric.dist_diff_le : forall M a b c e,
  CReal.le (CReal.abs (CReal.add (M.dist a b) (CReal.neg (M.dist c e))))
           (CReal.add (M.dist a c) (M.dist b e))
```

— the four-point reverse triangle inequality. It is two applications of the
shipped `Metric.dist_quadrilateral` (one per sign) closed by `CReal`'s
two-sided-to-`abs` lemma. Applied at `(a,b,c,e) := (x m, y m, x n, y n)` and
combined with `Metric.RegularSeq`'s two bounds it gives
`|D m - D n| <= 2/(m+1) + 2/(n+1)`, i.e. `K := 2`, and
`scaledCauchy_of_abs_diff_le` carries it to `K + 2 = 4`.

**That is the whole new-mathematics budget: one metric-level estimate.**
Everything else is record-field bookkeeping over shipped limit algebra.

### Sizing, re-measured

| piece | new estimates | shipped lemmas consumed |
| --- | --- | --- |
| carrier predicate + carrier | 0 | `Metric.CauchyAt`, `Subtype` |
| `Metric.dist_diff_le` | **1** | `Metric.dist_quadrilateral`, `CReal` abs/order |
| `dist` (total, named) | 0 | the three `scaledCauchy`/`speedup` bridges |
| the 12 record fields | 0 | `converges_*` (14 of 33) |
| isometric embedding + density | 0 | `converges_of_equiv`, `Metric.dist_self` |
| completeness of the completion | not sized here | — |

Against ADR-1625's "four lemmas plus a speedup bridge plus one undeclared
predicate" (six units), the re-measured figure is **one new estimate**, and the
predicate is a rename of something shipped.

## Consequences

- ADR-1625's section "What a generic completion would actually cost" is
  superseded in full. Its carrier line is right up to the missing predicate; its
  cost line is measured against a term former the development abandoned.
- `CReal.limit`, `CReal.RegularSeq`, `CReal.limitSeq`, `CReal.limitSeq_regular`
  and `CReal.limit_dist` remain with **zero consumers**. This ADR does not add
  any. They are not deleted (they are the readable statement of Bishop
  completeness), but no future sizing should route through them: the live
  construction is `mk` after `speedup` after `diagonal`.
- The general rule worth carrying: **when a development has two constructions
  for the same object, a cost estimate must be taken against the one that has
  consumers.** ADR-1625 counted lemmas about the named-in-the-doc route and
  concluded a four-lemma gap; the route with consumers had already closed it.
  The check is one grep for uses, not for declarations.
- A second, narrower rule: **"stated about the concrete carrier" is not
  evidence of non-reusability when the generic construction's own data lives on
  that concrete carrier.** `Metric.dist` being `CReal`-valued is what makes the
  entire `CReal` limit algebra generic-metric machinery.

## Alternatives rejected

**Prove ADR-1625's four lemmas about `CReal.limit` anyway.** Rejected: it adds
four declarations to a five-declaration island that would still have no
consumers, and the completion built on it would carry the factor-of-two
overshoot `creal.rs` documents.

**Existential modulus in the carrier** (`Subtype (Nat -> M.carrier)
(Metric.Cauchy M)`). Rejected on a kernel fact, not on taste: `Metric.Cauchy` is
`exists K, ...`, a `Prop`, and the `dist` field needs `K` as data. This is the
first mutant run in this lane.

**`Sigma Nat (fun K => Subtype (Nat -> M.carrier) (fun f => Metric.CauchyAt M f K))`**
— carry the modulus as data instead of fixing it at 1. Rejected: it makes the
carrier's `equiv` compare sequences with different moduli, so every field
witness carries a modulus-combination step, for no gain — any `CauchyAt M f K`
sequence is `RegularSeq` after reindexing, and the reindexing is
`CReal.speedup`'s own `Nat` index shape, already available.
