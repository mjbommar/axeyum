# 02 — Constructive analysis

Reviewer: a Bishop-school constructive analyst
Verdict, 2026-09-06: **excited, and for a different reason than two days ago**
Last measured: 2026-09-06 at `5f4c38c32`

> "Almost nobody builds this. You have a working constructive real line with
> integration on it and no choice anywhere. Where is the fundamental theorem
> of calculus?"
>
> **Answered 2026-09-04: it was already there, and the reviewer had missed it.**
> Both directions were admitted 2026-08-27, a week before this file was
> written.
>
> **All five of the reviewer's 2026-09-04 items are now closed** (2026-09-06).
> The subject is no longer the line: there is a metric layer, ℝⁿ, an
> integration space and L¹ above it. So the question changes:
>
> "Five things here are `Metric`s: the line, the plane, ℝⁿ at every dimension,
> L¹, and the product. There are exactly **three** completeness theorems, and
> they cover the line, a closed real interval, and the product. **So the plane,
> ℝⁿ and L¹ are not complete as far as this kernel is concerned** — and there
> is no completion. Which is it?"

**Correction, recorded 2026-09-04, and it recurred this week.** The first
version of this review said the fundamental theorem of calculus was missing and
made it the reviewer's number-one item. That was **false**.
`CReal.hasDerivative_antiderivative` (`1b91195d0`) and
`CReal.integral_eq_antideriv_diff` (`d1bdae9e7`) were both admitted on
2026-08-27, with empty axiom footprints and registered facts (re-confirmed
2026-09-06: both `proved`, `axiom_footprint` `[]`, as are the `_of_uc` pair,
`integral_by_parts`, `mvt_interiorExtremum`, `weierstrassMTest` and
`ivt_bisect_approx`).

The cause was measured rather than guessed, and it is systemic. Re-measured
2026-09-06: **314 of the 485 `CReal` facts (64.7%), and 1,095 of 2,954
ledger-wide (37.1%), carry `gen-kernel-facts.py`'s mechanically-generated
prose**, which opens by stating that it deliberately makes no mathematical
characterisation of the theorem. The generator's refusal is correct and is part
of why the ledger is trustworthy. The defect is that nothing distinguishes *no
prose has been written* from *there is nothing here* — so the ledger answers "is
X proved?" and cannot answer "what do we have?", which is the question a review
is built from. ADR-1605 proposes the fix.

**Two 2026-09-06 measurements say the defect is not shrinking, it is moving to
the new shelves.**

- The reviewer's own item 2, the radius of convergence, landed on 2026-09-05 —
  and **all seven of its ledger rows are `[generated]`**
  (`F:creal-powerseriesconvergeswithinradius`,
  `F:creal-powerseriescauchywithinradius`, `F:creal-powerseriestermradiusbound`,
  `F:creal-abs-pow-le`, `F:creal-one-pow`,
  `F:creal-expseriespartialispowerseries`,
  `F:creal-cosseriespartialispowerseries`). A reader running the same query that
  produced this file's original error would make it again, on this file's own
  headline item.
- **The ledger names 487 distinct `CReal.*` kernel declarations against 629
  admitted** — 142 uncovered — and for the layers above the line it is far
  worse: **17 ledger rows against 253 admitted declarations** across `Metric`
  (9 of 97), `RN` (2 of 58) and `IntSpace` (6 of 98). The curated rows that do
  exist are good; there are just very few of them.

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605). Every absence claim in the 2026-09-06
> rewrite below was re-derived from a kernel build, not from prose.

## The persona

Works in the tradition of Bishop's *Foundations of Constructive Analysis*:
every existence claim carries a construction, every real number carries a
modulus, and the law of excluded middle is not available. Has spent a career
explaining that constructive analysis is not a restriction of classical
analysis but a different and more informative subject. Instinctively checks
two things in any formalization: whether countable choice was smuggled in, and
whether "not equal" was used where apartness was meant.

## What the library has today

**485 proved ℝ facts, zero open, all with empty axiom footprint** — and, in the
kernel itself, **629 admitted `CReal` declarations** (`shape_search
--include-constructed --list-namespaces` at `5f4c38c32`: 4,765 declarations
across sixteen groups, 30 of them axioms — and no `CReal` fact's
`axiom_footprint` names any of them).

ℝ is a Bishop setoid of regular sequences of rationals
([ADR-0512](../research/09-decisions/adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md)),
with `CReal.Equiv` as the equivalence and apartness carried as positive data
rather than as a negation.

| area | what exists |
|---|---|
| the line | `CReal` as regular sequences, `Equiv`, apartness (`apart_congr`, `apart_symm`), order, `max`/`min`, absolute value |
| completeness | `converges_of_cauchy`, `converges_of_scaled_cauchy`, `converges_le`, `converges_lower_bound`, `limit_dist` |
| suprema | `supOn`, `supOn_ub`, `lubSet`, sup at fine mesh points |
| continuity | `UniformlyContinuousOn`, `evtLinear_uniformly_continuous` |
| differentiation | 25 `hasDerivative*` declarations — `_const`, `_id`, `_add`, `_mul`, `_chain`, `_pow`, `_unique`, `HasDerivativeOn` — plus Fermat, Rolle and the constructive MVT at an interior extremum |
| integration | Riemann sums with an interval-relative mesh: `riemannSumTotalEpsLe`, `riemannSumDeepCauchyFolded`, mesh refinement, splitting, additivity |
| transcendentals | `expFn`, `sinFn`, `cosFn` as total `CReal → CReal` with uniform convergence, derivatives and uniform continuity; `exp` with dominant-term bounds, `cosOneConverges`, π with `twoLePi` and the half-term bounds, `sqrt` with `sqrt_mul` |
| **power series** | `powerSeriesPartial` with a **radius carried as data** — `powerSeriesTermRadiusBound`, `powerSeriesCauchyWithinRadius`, `powerSeriesConvergesWithinRadius`, plus `abs_pow_le` and `one_pow`; `expSeriesPartialIsPowerSeries` and `cosSeriesPartialIsPowerSeries` exhibit the hand-built shelves as instances (2026-09-05, ADR-1638) |
| series tests | `sumRange_comparisonTest`, `sumRangeRatioTest`, `geomCauchyOfLt`, `sumRange_cauchy_of_dominated`, the alternating-series brackets, `weierstrassMTest` |
| uniform convergence | `UniformConvergesOn`, `uniform_limit_uniformly_continuous`, `hasDerivative_uniform_limit` |
| algebra of the line | `left_distrib`, `pow_le_pow_of_one_le`, `pow_nonneg`, `pow_le_one`, `eq_zero_of_mul_self_zero` |
| the theorems | intermediate value (`ivt_bisect_approx`, by bisection with an explicit modulus), extreme value |
| **the FTC, both directions** | `hasDerivative_antiderivative` and `integral_eq_antideriv_diff` (2026-08-27), plus `integral_by_parts`; and from 2026-09-04 the `_of_uc` forms that drop the redundant boundedness witness, since `bounded_of_uniformly_continuous` *computes* it from the continuity witness the caller already supplies |
| structure | `CReal.commRingS`, `CReal.orderedRingS`, `CReal.addGroupS`, and from 2026-09-05 **`CReal.fieldS : AlgS.Field`** over the setoid algebra spine |

The IVT is proved the way this reviewer would want it proved: by bisection,
producing an approximate root to any requested precision, not by asserting a
classical existence.

### And, since 2026-09-04, four layers above the line

Every one of these is new since the first version of this review, and every one
of them has an empty axiom footprint on every registered fact.

| layer | declarations | what it is |
|---|---|---|
| `Metric` | **97** | a 12-field metric-space record (ADR-1602); `Metric.creal` and `Metric.cpoint` as instances; `Complete`, `TotallyBounded`, `Compact` and their `*On` twins; uniform and pointwise continuity over an *arbitrary pair* of spaces; `evt_approx_max` — the EVT over any totally bounded subset of any metric space, with completeness never used |
| `RN` | **58** | ℝⁿ as `Nat → CReal` with the dimension in the equivalence, not the type (ADR-1606); unsquared Cauchy–Schwarz at **symbolic** dimension, Minkowski, `RN.metric` one metric space per `n`, and `CPoint` proved to be the n = 2 case |
| `IntSpace` | **98** | a predicative pre-integration space (ADR-1612), 16 fields, three instances sharing no machinery — the Riemann interval integral, finite sums, a Dirac space — with **measure derived from the integral**; and (ADR-1625) `IntSpace.bundledL1`, the L¹ pseudometric as a `Metric`, with `crealIntervalL1` and `crealFiniteL1` |
| `Metric.prod` | **12** | the max metric on a `Sigma` pair, both projections 1-Lipschitz, and completeness transfer (ADR-1639) — built in a **sibling prelude**, see the reservation below |

Bishop compactness is here in Bishop's own form: `TotallyBounded` **plus**
`Complete`, no covers, and the closed real interval proved to satisfy it
(`Metric.creal_compactOn_interval`). The interval EVT via `CReal.supOn` and the
interval EVT via the general metric theorem carry the same interned `ExprId`,
built by separate code in two modules — the instance claim is a measurement,
not a reading.

## Their verdict

This is one of the more complete machine-checked constructive real analyses in
existence, and the reviewer would know, because the comparison set is small.
Four things earn their respect specifically:

**Apartness is data, not negation.** The library carries `apart` as a positive
witness and the setoid spine (`AlgS`) was built precisely so congruence
obligations are explicit fields rather than rewriting. That is the correct
design and it is the one most formalizations get wrong.

**No choice, anywhere.** The footprints are empty — measured 2026-09-06 across
all 485 `CReal` facts and all 17 `Metric`/`RN`/`IntSpace` facts, zero with a
non-empty `axiom_footprint`. Bishop's own development uses countable choice
freely and modern constructivists argue about whether it should; a development
that avoids it entirely is a stronger artifact than Bishop's book.

**Integration exists, and it is now abstract.** Most constructive
formalizations stop at continuity. What is here is a pre-integration space in
the Petrakis–Zeuner sense (arXiv:2207.08684) with measure *derived* from the
integral, reached by an "axioms come from what the development proves"
discipline before the paper was read — so the switching cost was zero.

**The classical principles enter as binders, never as axioms.**
`IntSpace.monotone_convergence_of_real` is monotone convergence with "every
bounded monotone real sequence converges" as an explicit hypothesis in the
type, and the fact says in as many words that the gap between its constructive
and classical members is LPO-strength and is a statement about ℝ, not about
integration. The constructive members (`integral_mono_step`,
`integral_seq_le`) are proved outright. This is exactly how a Bishop-school
reviewer would want a classical theorem shelved.

Their reservation is no longer about the line. It is that **the word "complete"
is doing more work in the prose around this library than in its kernel**. See
below.

## What they would say is missing

- ~~**A general power series theory.**~~ **CLOSED 2026-09-05.**
  `CReal.powerSeriesConvergesWithinRadius` at `5f4c38c32`, footprint `[]`; the
  radius is data (a coefficient bound `|aₖ|·Rᵏ ≤ M` plus a caller-supplied
  ratio `0 ≤ r < 1` with `|x| ≤ r·R`), because over `CReal` the order is
  undecidable and a supremum cannot be manufactured from `|x| < R`.
- ~~**Uniform convergence as a first-class notion.**~~ **[AUDIT] present**:
  `CReal.UniformConvergesOn`, `uniform_limit_uniformly_continuous`,
  `hasDerivative_uniform_limit`, `weierstrassMTest`, all 2026-08-27 (audit row
  A3).
- ~~**Constructive metric spaces.**~~ **CLOSED 2026-09-04** (W2-1/W2-2,
  ADR-1602/1607): 97 `Metric` declarations, `Metric.Complete` generalized off
  ℝ, continuity over an arbitrary pair of spaces.
- ~~**The Bishop compactness apparatus.**~~ **CLOSED 2026-09-04** (W2-3):
  `TotallyBounded`, `TotallyBoundedOn`, `CompactOn`, `evt_approx_max` assuming
  total boundedness alone, and the closed real interval as an instance.
- ~~**Multivariate anything.** No ℝⁿ.~~ **PARTLY CLOSED 2026-09-04** (W2-4,
  ADR-1606): ℝⁿ exists with inner product, norm, Cauchy–Schwarz at symbolic
  dimension, and a metric per dimension. **No multivariate *calculus*, and this
  is now a precise claim**: `crates/axeyum-lean-kernel/src/rn.rs` declares 58
  names — `dot`, `norm`, `smul`, `metric`, the `CPoint` bridge — and **not one
  derivative, partial derivative or integral among them**.

What is actually missing today, in the reviewer's order:

- **Completeness, everywhere it is implied.** `Metric.Complete` is a
  definition; the theorems proving it are `Metric.creal_complete`,
  `Metric.creal_completeOn_interval` and `Metric.prod_complete` — and that is
  the whole list. **The Euclidean plane, ℝⁿ at symbolic `n`, and L¹ each have
  no completeness theorem.** For the plane this is not a formality:
  `Metric.cpoint` is related to `Metric.prod Metric.creal Metric.creal` by a
  **carrier equivalence only, not an isometry** (Euclidean distance against max
  distance), so `prod_complete` does not transport to it.
- **A completion.** There is no `Metric.completion`. `CReal` is not the
  completion functor applied to ℚ and cannot be made one — `Metric.dist` is
  `CReal`-valued, so a `Metric` on ℚ presupposes ℝ, and `CReal`'s regularity is
  stated on rational samples, a shape no general metric carrier has (ADR-1625).
  ADR-1625 measured the reuse at **1 of the 33 declarations** in
  `creal/completeness.rs` and `creal/convergence.rs` (`CReal.limit`, zero
  algebra lemmas, zero consumers) — that number is the lane's, not re-derived
  here. What *is* re-derived here: `Metric.Regular`, the regularity predicate
  the ADR's proposed carrier needs, **is not declared** (the eight `Regular`
  hits in `metric.rs` are all `ReducibilityHint::Regular`). This is the single
  item that would change the most: it makes every `Metric` in the library
  completable at once, L¹ included.
- **The product metric is proved but not joined.** `build_metric_prod_prelude`
  is called by nothing except its own tests and its own inventory example —
  measured by grepping every caller in the crate — so the twelve `Metric.prod*`
  declarations are absent from the metric closure `shape_search
  --include-constructed` builds (97 `Metric.*` declarations, **none** of them
  `Metric.prod*`). The facts are real and axiom-free; they are simply not
  reachable from the shelf that would use them.
- **`sin` is not yet an instance of the power series.** `power_series.rs`
  declares eight names; `expSeriesPartialIsPowerSeries` and
  `cosSeriesPartialIsPowerSeries` are there and `sinSeriesPartialIsPowerSeries`
  is not. Termwise sum and scalar multiple inside a common radius are also
  unbuilt.
- **Tightness of ℝ's apartness.** `CReal.fieldS : AlgS.Field` landed
  2026-09-05, but `AlgS.Field.IsTight CReal.fieldS` is deliberately **not**
  declared: its proof needs `¬(lt x y) → le y x`, i.e. a single-index
  introduction rule for `CReal.lt`, and no such lemma exists among `CReal`'s
  order theorems. `Rat` has its tight instance; ℝ does not. For this reviewer
  that is the most interesting open statement in the file.
- **Measure theory as a subject.** Measure is *derived* from the integral and
  its two bounds are proved, but **no `IntSpace` declaration's name contains
  "additive" or "sigma"**, and the only convergence theorem,
  `monotone_convergence_of_real`, carries the classical principle as a binder.
  Nothing here lets you integrate a function that is not already handed to you
  with a modulus.

## The blocker

Two of a fundamental kind now, where the 2026-09-04 review said none.

**A large-elimination wall, and it is the good kind of finding.** ADR-1627:
`CReal.inv : (x : CReal) → (k : Nat) → PosBound x k → CReal` takes the modulus
as **data**, while `CReal.Apart x zero` is `Or (lt x zero) (lt zero x)`, a
`Prop`, and `pos_bound_of_lt` hands the modulus over only inside an `Exists`,
also a `Prop`. Neither the sign nor the modulus can be eliminated out of a
`Prop` into a `CReal`, so a **functional** constructive field is undefinable
here. `AlgS.Field`'s `mulInvEx : ∀ a, apart a zero → ∃ b, equiv (mul a b) one`
is a `Prop`, both eliminations are legal, and ℝ is a field in exactly that
existential sense. This is a real theorem about the setting, not a missing
lemma, and it is why tightness is a predicate on the record rather than a
field.

**No completion construction.** ADR-1625 sizes it at four new `CReal.limit`
lemmas — `limit_congr`, `limit_le`/`limit_nonneg`, `limit_add` — plus a
`speedup` bridge, all claimed provable from `CReal.limit_dist` alone, over the
carrier `Subtype (Nat → M.carrier) (Metric.Regular M)`. The universe half of
that is real: `Sigma`/`Subtype`/`PSigma` landed (W0-5, `c0054fd3b`; the census
reads `Sigma` 8, `PSigma` 5, `Subtype` 7), so **the `Sigma`/`Subtype` blocker
named on 2026-09-04 is gone** — do not repeat it. The predicate half is not:
`Metric.Regular` does not exist yet, so the sizing counts four lemmas and one
undeclared predicate.

Two practical constraints still slow everything:

**Build cost.** The ℝ prelude is **171,157 lines of Rust across 110 files**
(`creal.rs` plus `creal/**.rs`; 158,179 excluding `*test*` files), and its
pinned stack requirement is **16 MiB in debug, 8 MiB in release**
(`artifacts/kernel-stack-envelope.tsv`, measured 2026-08-28). A single new deep
declaration has repeatedly broken unrelated tests, and the new layers inherit
the cost: `build_intspace_prelude` now calls `build_metric_prelude`, and a
`shape_search --include-constructed` build of all sixteen groups took **166–209 s**
across two runs on a box at load 14–22 this afternoon. See
[prelude-build-cost.md](../contributor-guide/prelude-build-cost.md).

**Setoid overhead.** Every construction over ℝ must carry its congruence
obligation explicitly. The `AlgS` spine that landed 2026-09-03 was built to
make this systematic; before it, congruence was rediscovered per lemma. The
`metric-compactness` lane measured the shape of the residual cost: the general
theorems are cheap and the **instances** are where the work is — its own count
was 34 declarations for every carrier against 10 more for one real interval.

## The 2026-09-04 Next Five — all five now closed

- [x] **1. The fundamental theorem of calculus.** ~~Both directions, over the
      existing Riemann integral, with an explicit modulus.~~ **Already proved
      2026-08-27; the item was the reviewer's error.** What did land on
      2026-09-04 is the pair of `_of_uc` forms with the redundant boundedness
      witness removed, and the finding that the constructive MVT is *not* a
      prerequisite: FTC-II routes through `constant_of_zero_deriv`, and the
      uniformity of the modulus replaces the MVT's asserted point.
- [x] **2. Power series with a radius of convergence** — *landed 2026-09-05*
      (`ed30eb7f9`, ADR-1638): eight declarations, footprint 0, the radius
      carried as a ratio witness rather than a supremum, and `exp` and `cos`
      exhibited as instances by proved `Equiv`. The comparison, ratio and
      geometric tests turned out to already exist and were reused. **Residue:**
      `sin` is not yet an instance, and termwise sum and scalar multiple inside
      a common radius are unbuilt.
- [x] **3. Uniform convergence and the interchange theorems.** **[AUDIT]
      Already proved 2026-08-27**, including the Weierstrass M-test. Audit row
      A3.
- [x] **4. A constructive metric-space carrier** — *landed 2026-09-04*
      (`b7df58b7b`/`5bb30b809`, ADR-1602/1607). 97 `Metric` declarations with
      completeness, Bishop total boundedness and the EVT over an arbitrary
      space; ℝ, the plane, ℝⁿ (`RN.metric`) and L¹ (`IntSpace.bundledL1`) are
      all instances, so ℝ is no longer the whole subject. **What the item asked
      for and did not get: the instances' own completeness** — see the
      reservations above.
- [x] **5. Differentiability on an interval, with the mean value theorem in
      its constructive form.** **[AUDIT] Already proved 2026-08-27**:
      `fermat_interiorExtremum`, `rolle_interiorExtremum`,
      `mvt_interiorExtremum`. Audit row A8.

## Next five, in their priority order (2026-09-06)

- [ ] **1. A generic `Metric.completion`.** Carrier
      `Subtype (Nat → M.carrier) (Metric.Regular M)`, distance
      `CReal.limit (fun n => M.dist (f n) (g n))`. ADR-1625 sizes it at four
      `CReal.limit` lemmas plus a `speedup` bridge, all from `limit_dist`; add
      to that the `Metric.Regular` predicate, which this review measured absent.
      It is worth more than any single space's completeness because it makes
      every `Metric` in the library completable at once — and it is what turns
      L¹ from a metric space into a complete one.
- [ ] **2. Completeness of the spaces that are already built**: the Euclidean
      plane, ℝⁿ at symbolic `n`, and L¹. ℝⁿ's is coordinatewise from
      `CReal.converges_of_cauchy` and the `rn-carrier` lane sized it at one
      undeclared bound, `|uᵢ − vᵢ| ≤ d(u,v)` — **that sizing is the lane's
      claim and this review did not re-verify it**. The plane's needs either an
      isometry to `Metric.prod Metric.creal Metric.creal` or a direct proof,
      because only a carrier equivalence exists today.
- [ ] **3. Join the product metric to the metric prelude**, so
      `Metric.prod_complete` is reachable from the shelf that would consume it,
      and finish the `←` direction of "continuous into the product iff
      continuous in both components". Small, and it is currently a
      lane-isolation artifact rather than a design decision.
- [ ] **4. Differential calculus on ℝⁿ.** A derivative for `RN.Vec → CReal`,
      partial derivatives, and the constructive inverse/implicit function
      statement. `rn.rs` has the norm and the metric and no calculus at all;
      this is the layer that turns a carrier into a subject, and every
      multivariate item the department asked for waits on it.
- [ ] **5. Tightness of ℝ's apartness**, i.e. a single-index introduction rule
      for `CReal.lt` (`x_n − y_n > 2/(n+1)` implies `y < x` with an explicit
      rational gap), and then `AlgS.Field.IsTight CReal.fieldS`. Constructively
      true of the Bishop reals, currently unprovable here, and the one open
      statement in this file a Bishop-school analyst would want to own.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: 476 proved ℝ facts, zero open. Riemann integration, IVT by bisection, EVT, uniform continuity, suprema, exp/cos/π/sqrt, `CReal.orderedRingS`. **Claimed no FTC — this was false.** | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Correction.** The FTC was proved 2026-08-27, before this file existed. Cause measured: 64% of `CReal` facts carry generated prose that makes no mathematical claim. Lane `ftc` added `hasDerivative_antiderivative_of_uc` and `integral_eq_antideriv_diff_of_uc` (arity 5 and 7, down from 7 and 9), each footprint 0, and established that the constructive MVT is not a prerequisite. `creal::` 230 passed. Next Five items 2–5 are **not** re-verified and are under audit. | `182d0dd7d`; ADR-1597 |
| 2026-09-04 | **A finding about this shelf from roadmap W3-1**: generalizing `CReal.integral` into an integration-space record re-derived only 1 of 6 interval theorems, because the theorems this reviewer admired — linearity, monotonicity, the absolute bound — are precisely the record's axioms, not its consequences. The `Integrable` predicate had to be `Sort 1` rather than `Prop`, since `UniformlyContinuousOn` is data whose modulus the integral consumes. And a stale blocker fell: `uniformly_continuous_abs` was written into the ADR as absent, then found derivable from `uniformly_continuous_max`/`_min` because `abs` is `max x (neg x)` by definition. | `3d5320f68` |
| 2026-09-05 | **Item 2 landed** (roadmap W2-5, ADR-1638): `CReal.powerSeriesPartial` converges inside a radius given as data (coefficient bound plus a ratio strictly below one), and `expSeriesPartial`/`cosSeriesPartial` are proved `Equiv` to the generic series at their coefficients — so the hand-built exp and cos shelves are now instances. The comparison, ratio and geometric tests were already here; the reviewer's audit row A10 undercounted them because `shape_search` does not index `creal`. Termwise sum and scalar multiple inside a common radius are the short residue. | `ed30eb7f9` |
| 2026-09-06 | **Re-measured against `main`, whole file rewritten.** ℝ facts 476 → **485**, still zero open and zero non-empty footprints. Kernel census (`shape_search --include-constructed --list-namespaces`, 4,765 declarations, build 166–209 s over two runs): `CReal` **629**, `Metric` **97**, `RN` **58**, `IntSpace` **98**, each re-listed name by name with `--ns`. All five 2026-09-04 items are closed: item 4 by the metric layer (W2-1/2/3, ADR-1602/1607), item 2 by the power series (W2-5, ADR-1638), items 1/3/5 by the audit. New above the line: ℝⁿ (W2-4, ADR-1606), the integration space and L¹ as a metric space (W3-1, ADR-1612/1625), the product metric (W2-10, ADR-1639), and `CReal.fieldS : AlgS.Field` (ADR-1627). Four claims changed direction: the transcendentals-are-ad-hoc reservation is retired; the metric, compactness and ℝⁿ absences are closed; the `Sigma`/`Subtype` blocker is gone (`c0054fd3b`); and **the blocker section gained two of a fundamental kind** — the large-elimination wall that forces an existential field, and the absent completion functor. Three new measured absences: `Metric.Complete` is proved for ℝ, real intervals and binary products **only** (the plane, ℝⁿ and L¹ have none); `build_metric_prod_prelude` is called by nothing but its own tests, so no `Metric.prod*` name is in the metric closure; and `rn.rs` declares no derivative or integral. The ledger defect that caused this file's original error **recurred on this file's own headline item**: all seven power-series facts are `[generated]`, and the ledger names 487 of 629 `CReal` declarations and 17 of 253 `Metric`/`RN`/`IntSpace` ones. **In flight, not on main:** one live worktree (lane `supon-r6b`) carries three WIP `CReal` commits — `meshLevelCount_pow` and `hclose_of_uc` for `supOn` rung 6 — whose own messages say the kernel has not accepted them yet; nothing in this file counts them. | measured at `5f4c38c32`; census, `artifacts/facts/`, `artifacts/kernel-stack-envelope.tsv` |

## How to re-measure

```sh
# the ledger view (the number the verdict quotes)
python3 - <<'PY'
import json, glob, collections
c = collections.Counter()
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f))
    if (d.get('formal') or {}).get('fragment') == 'CReal': c[d.get('epistemic_status')] += 1
print(c)
PY

# the KERNEL view, which is the larger number and the one the ledger misses.
# `CReal`, `Metric`, `RN` and `IntSpace` are CONSTRUCTED namespaces: without
# --include-constructed shape_search does not index them and answers
# UNANSWERABLE, which is not the same as ABSENT. Takes ~3.5 min on a loaded box.
cargo build --release -p axeyum-lean-kernel --example shape_search
target/release/examples/shape_search --include-constructed --list-namespaces
target/release/examples/shape_search --include-constructed --ns Metric --limit 300

# how much of that the ledger characterises (ADR-1605)
python3 - <<'PY'
import json, glob
tot = gen = 0
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f)); tot += 1
    gen += d.get('title', '').startswith('[generated]')
print(f'{gen}/{tot} generated prose = {gen/tot:.1%}')
PY
python3 scripts/count-landmark-facts.py

# the ℝ suite needs release + a deep stack (NOT run in the 2026-09-06 pass)
RUST_MIN_STACK=1073741824 scripts/cargo-serialized.sh test --release \
  -p axeyum-lean-kernel --lib -- creal:: --test-threads=4
```

## Related

- [03-classical-analysis.md](03-classical-analysis.md) — the same shelf, judged
  by someone who wants measure theory
- [04-algebra.md](04-algebra.md) — why ℝ is a setoid and not a quotient, and
  where `AlgS.Field` comes from
- [06-topology.md](06-topology.md) — the metric layer read as topology, and
  ADR-1602's decision not to have open sets
- [diary-constructive-ivt.md](../mathematics-2026-08/diary-constructive-ivt.md),
  [diary-apart-as-data.md](../mathematics-2026-08/diary-apart-as-data.md)
