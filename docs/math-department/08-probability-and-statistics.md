# 08 — Probability and statistics

Reviewer: a probabilist, with a statistician looking over their shoulder
Verdict, 2026-09-06: **the finite shelf now builds its own distributions and
beats Chebyshev's rate; the missing object is a product space, not a measure**
Last measured: 2026-09-06 at `97ce06aff`

> "Two days ago I said everything above this shelf was behind measure theory.
> That was wrong in both directions. There *is* a measure now — derived from
> an integral, not assumed — and it did not unlock a single thing I asked for.
> What is actually in my way is smaller and more embarrassing: there is no
> product space, so I cannot write down two random variables that live
> together."

**Correction, recorded on creation.** The first pass of this review said the
library contained "one item, a Cauchy-Schwarz inequality over the rationals."
That was wrong, and it was wrong because the reviewer searched for
`probability_space` and `random_variable` — Mathlib's names — rather than for
the shape. This is the exact failure mode the contributor guide warns about:
*search for the step, not the name*, and an empty result from a tool never
pointed at your subject is indistinguishable from a strong negative.

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

## The persona

Works with measure-theoretic probability: probability spaces, random variables
as measurable functions, expectation as an integral, and the limit theorems.
The statistician beside them cares about estimators, confidence, and
concentration inequalities, and is happier than the probabilist with a finite
model.

## What the library has today

**A finite/discrete probability theory, 74 kernel declarations, all
axiom-free — 54 at ℚ (8 definitions, 46 theorems) and 20 stated once over
`(R : AlgS.OrderedRing)` (7 definitions, 13 theorems), which covers ℚ and ℝ
in one statement.** A random variable is a rational-valued function on a
finite index range; `Rat.expectation X p n` is `∑_{k<n} X(k)·p(k)` against a
**weight function** `p` carrying an `IsDistribution p n` hypothesis. One
weight function, one index range — that shape is the whole story of what this
shelf can and cannot state.

| layer | theorems |
|---|---|
| expectation | `expectation_add` (linearity), `expectation_const`, `expectation_smul`, `expectation_sumVars`, `expectation_le`, `expectation_nonneg` |
| events | `prob_le_one`, `prob_complement`, `uniform_is_distribution` |
| indicators | `indicator_nonneg`, `indicator_le`, `expectation_indicator_le_one`, `variance_indicator`, `variance_indicator_le_quarter` |
| variance | `variance_eq` (the computational formula), `variance_smul`, `variance_add_eq`, `variance_add_of_uncorrelated`, `variance_sumVars`, `variance_scaled_mean`, `variance_scaled_add_nonneg`, `variance_nonneg` |
| covariance | symmetry, `covariance_add_right`, `covariance_smul_left`, `covariance_sumVars`, `covariance_sumVars_left` (bilinearity) |
| inequalities | `Rat.markov_inequality`, `Rat.chebyshev_inequality`, Cauchy–Schwarz for covariance in all three cases (positive variance, zero variance, general) |
| sample means | `variance_sampleMean_uncorrelated`, `chebyshev_sampleMean_uncorrelated`, `weak_law_of_large_numbers`, `bernoulli_law_of_large_numbers` |
| distributions | `AlgS.OrderedRing.bernoulliMass`/`bernoulliVar` with `bernoulli_isDistribution` **proved from the construction**, `bernoulli_expectation`, `bernoulli_variance`; `Rat.binomial_expectation`, `binomial_variance`, `binomial_chebyshev` |
| fourth moment | `Rat.FourwiseUncorrelated`, `expectation_sumVars_mul`, `expectation_sq_sumVars_mul_sq`, `fourth_moment_inequality`, **`fourth_moment_sumVars_le`** (`E[(Σ Y_i)⁴] ≤ Σ M₄ + 3(Σ σ²)²`) and **`fourth_moment_tailSumVars`** |
| the generic layer | `AlgS.OrderedRing.{IsDistribution, expectation, variance, covariance, Independent}`, linearity, Markov, `variance_nonneg`, `expectation_map`, `uncorrelated_of_independent` |

Two rows are the substantive ones. `chebyshev_sampleMean_uncorrelated` is the
concentration bound that makes the weak law work, stated for pairwise (not
full) independence, which is the sharp hypothesis. `fourth_moment_tailSumVars`
is a **`1/m²` tail where Chebyshev on the same shelf gives `1/m`** — the first
Hoeffding-class rate this carrier reaches, and it needs neither a joint law
nor an exponential.

**The integration side exists and is separate.** `IntSpace` is a predicative
pre-integration space, **98 declarations, every one derived and axiom-free**
(pinned by `every_intspace_declaration_is_present_and_derived` and
`every_intspace_declaration_is_axiom_free`). It carries `IntSpace.measure`
*derived* as the integral of an integrable indicator, with `measure_nonneg`,
`measure_le_total`, `measure_univ`, `measure_const` and
`measure_witness_independent`; a `countingMeasure`; a Dirac probability space
(`crealDirac`, `dirac_measure_detachable`); the L¹ metric family
(`l1Dist` with `_nonneg`/`_self`/`_comm`/`_triangle`, `bundledL1`,
`crealFiniteL1`, `crealIntervalL1`); `MonotoneConvergence` as an ADR-0603
graded family; and the two bridges to this shelf,
`IntSpace.crealFinite_expectation` and `IntSpace.ratExpectation_integral`.

## Their verdict

**The statistician is pleased and has stopped being startled.** Bilinear
covariance, the variance of a sum under uncorrelatedness, Markov and
Chebyshev, a concentration bound on the sample mean, a *constructed* Bernoulli
model whose `IsDistribution` obligation is discharged rather than hypothesised,
the binomial's mean and variance, and a fourth-moment tail that is genuinely
sharper than Chebyshev. Everything an introductory mathematical-statistics
course proves in its first third is here, over an exact rational carrier with
no floating point and no assumed axioms. For finite-sample statistics — which
is most of what is actually computed in practice — this is usable today.

**The probabilist's objection has moved, and it got more specific.** The
09-04 reading said there was no probability *space* and that everything was
behind measure theory. Two days of work showed that diagnosis was wrong: a
measure landed, derived from an integral, and it unlocked none of the limit
theorems. What is actually in the way is that this development has **one
weight function over one index range**. There is no product of index ranges
and no joint law, so:

- **independence has to be *stated*, not defined**: `AlgS.OrderedRing.Independent`
  is the moment identity `E[A·B] ≃ E[A]·E[B]`, and
  `uncorrelated_of_independent` is a one-step consequence of it. There is no
  σ-algebra and no independence of families.
- **the product rule for expectations is unavailable**, which is exactly what
  blocks Hoeffding: it needs `E[∏_j f(X_j)] = ∏_j E[f(X_j)]`.
- limit theorems are still absent as *limits* — see the next section.
- continuous distributions, densities, and the normal distribution are absent.
- conditional expectation, filtrations, martingales, stochastic processes are
  absent.

Their assessment: this is a *combinatorial* probability library that has been
built well and further than the last reading gave it credit for. The next door
is smaller than measure theory and has to be opened first anyway.

## What they would say is missing

- **A product space and a joint law.** The one measured blocker, and the
  reason the previous two entries in this list were misdiagnosed. See below.
- **The limit theorems, as limits.** **[AUDIT] `Rat.weak_law_of_large_numbers`
  is proved** (2026-08-24, `54592604a`) — but the kernel's own documentation
  of it says it is *"a RENAMING, not a new result"* whose type is identical to
  `chebyshev_sampleMean_uncorrelated`'s, *"stated at each finite `m` rather
  than as a limit"*. So the finite-sample weak law is real and the
  **convergence statement is still absent**;
  `Rat.bernoulli_law_of_large_numbers` is the same shape instantiated at
  indicators. The strong law and the central limit theorem are absent.
- **Measure theory *on ℝ*.** `IntSpace.measure` exists and is derived, not
  assumed — but it is a measure on a pre-integration space's integrable
  indicators, not σ-algebras and Lebesgue measure on the line. See
  [03-classical-analysis.md](03-classical-analysis.md).
- **Named distributions beyond Bernoulli and binomial.** Bernoulli is
  constructed over the generic ordered ring; the binomial's mean, variance and
  Chebyshev bound are at ℚ only, because `variance_eq` needs `mulComm` and
  there is no `AlgS.CommOrderedRing`. The normal needs measure and the
  Gaussian integral.
- **Statistical inference.** Estimators, bias, consistency, confidence
  intervals, hypothesis tests.
- **Entropy and information theory.** Still blocked on logarithms: the `CReal`
  prelude interns exactly four `expFn`-family names (`expFn`,
  `expFn_one_equiv_e`, `expFnTermAbsLe`, `expFnUniformConverges`) and **no
  `log` or `ln` at all** — measured by the same query that found `expFn`, so
  the negative is not a blind one.

## The blocker

**One, and it is smaller than the one this file named two days ago.**

**There is no product space and no joint law, and this is measured, not
inherited from a lane report.** Searching the whole `Rat` namespace (543
declarations) and the whole `AlgS` namespace (390) for any name containing
`prod` or `joint` returns `Rat.PairwiseUncorrelated` and the five
`Rat.prodRange` declarations — and `prodRange : (Nat → ℚ) → Nat → ℚ` is the
finite product `∏_{j<n} f j`, built in `rat_prelude/sum_maps.rs` for
determinants. The whole `IntSpace` namespace (98 declarations, read off the
full 4,765-declaration `--include-constructed` index) contains nothing named
for a product either. The `prodRange` hits are their own positive control:
the query was not blind.

The consequence is precise, and it cuts the other way from what a reader
expects. `Rat.prodRange` means the *statement* `E[∏_j f(X_j)] = ∏_j E[f(X_j)]`
is writable today. What does not exist is any structure from which it could be
**derived** — and the shelf's own precedent (`Independent` is a moment
identity, not a σ-algebra condition) means the honest options are to build a
product of index ranges with a product weight, or to assume the `k`-fold
product rule the way the two-fold one is assumed. Those are different pieces
of work with different value, and choosing between them is the next decision
this shelf needs.

Hoeffding sits behind it, twice over: the product rule, and `CReal.expFn_add`,
which does not exist (verified above). Neither absence is about effort spent
on the exponential — `CReal.expFn` itself is there.

The far blocker is unchanged in kind but smaller than it was: **measure theory
on ℝ** — σ-algebras and the Lebesgue integral on the line, as against
`IntSpace`'s predicative integral — still needs topology and a design
decision. See [06-topology.md](06-topology.md) and
[03-classical-analysis.md](03-classical-analysis.md). Constructive measure
theory is additionally awkward, so this is not a transcription job.

The carrier question this file raised is **answered**: the `AlgS.OrderedRing`
spine covers ℚ and ℝ at once, 20 of the shelf's declarations are stated over
it, and `IntSpace.ratExpectation_integral` is the ℚ↔ℝ bridge in the only form
the carrier permits (the rational expectation is the finite integral across
`ofRat`, because `IntSpace` is hard-wired to real values).

## What the ledger says

**52 facts in `artifacts/facts/` name a declaration from this shelf, and every
one of them is `proved`** — zero `open`, zero `refuted`. Their evidence blocks
record an empty `Kernel::axiom_footprint`, and the tests that check them assert
`Environment::contains` **first**, because an absent name has an empty
footprint too.

Coverage, counted per declaration rather than by subtracting totals: **50 of
the 74 shelf declarations have a fact whose `formal.statement` declares that
name.** Of the 24 that do not, 15 are definitions, which this ledger largely
does not carry — but **9 are theorems**: the generic layer's
`AlgS.OrderedRing.expectation_{add,const,le,map,nonneg,smul}` and
`variance_nonneg`, and the two peeling lemmas
`Rat.expectation_sumVars_mul{,_eq_zero}`. Those are proved in the kernel and
uncharacterised in the ledger, which is ADR-1605's finding showing up on this
shelf specifically, and it is why the declaration count and the fact count are
both quoted here rather than one standing in for the other.

## Next five, in their priority order

- [x] **1. The weak law of large numbers.** **[AUDIT] Proved
      2026-08-24** (`Rat.weak_law_of_large_numbers`, `54592604a`), ten days
      before this review claimed it was one limit away; audit row A2. Recorded
      honestly: it is the finite-sample Chebyshev bound under the name a
      reader searches for, not a convergence statement. The limit form is item
      4 of the restated list below.
- [x] **2. Generalize the finite probability layer over `AlgS.OrderedRing`** —
      *landed 2026-09-04, `86c7a1065`, ADR-1616.* 29 declarations, footprint
      0; 9 of 11 attempted ℚ theorems are kernel-checked instances outright
      and 2 more with a stated adjustment. Measured today: 20 probability
      declarations under `AlgS.OrderedRing.*`.
- [x] **3. Independence as a definition** — *landed 2026-09-04, `86c7a1065`.*
      `AlgS.OrderedRing.Independent` and `uncorrelated_of_independent`, both
      present. It is the moment identity `E[AB] ≃ E[A]E[B]`, which is the
      strongest form the missing product space allows.
- [x] **4. Bernoulli and binomial distributions** — *landed `3e0ab5105`
      (ADR-1631) and `b92194ec7` (ADR-1653).* The Bernoulli model constructed
      on the generic carrier with `IsDistribution` proved; binomial mean,
      variance and Chebyshev at ℚ; and, in place of Hoeffding, the
      fourth-moment `1/m²` tail. Hoeffding itself did not land and is item 1
      of the new list.
- [ ] **5. Measure and the Lebesgue integral on ℝ**, once
      [06-topology.md](06-topology.md) and
      [03-classical-analysis.md](03-classical-analysis.md) settle their design
      decisions. **[~] Partly answered ahead of schedule:** `IntSpace` landed
      an integral-first predicative space with measure *derived* (98
      declarations, all axiom-free) and an L¹ metric. What remains under this
      heading is σ-algebras and Lebesgue measure on the line — and the
      measured lesson is that this was **not** what was blocking the limit
      theorems.

## The next five, restated for 2026-09-06

- [ ] **1. A product of index ranges with a product weight**, and the joint
      law it supports — or, with a written reason, the `k`-fold product rule
      assumed the way the two-fold one already is. Everything below waits on
      this choice.
- [ ] **2. Hoeffding**, once (1) exists and `CReal.expFn_add` is proved. Both
      absences are measured; neither is about the exponential's construction.
- [ ] **3. `AlgS.CommOrderedRing`**, so `variance_eq` and the three binomial
      theorems move from ℚ up to the generic carrier verbatim. Sized by the
      binomial lane as a record addition plus one migration.
- [ ] **4. Convergence in probability**, stated as a limit over the L¹ metric
      `IntSpace.crealFiniteL1` rather than as a family of finite bounds — the
      shape that turns the finite weak law into the weak law.
- [ ] **5. Register the 9 uncharacterised shelf theorems** — the generic
      layer's seven expectation lemmas and the two peeling lemmas — so the
      ledger stops under-reporting what the kernel has proved here.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: ~30 proved finite-probability theorems over ℚ — expectation, indicators, variance, covariance, Markov, Chebyshev, sample-mean concentration under pairwise uncorrelatedness. No measure theory, no limit theorems. **Correction:** the first review pass under-reported this shelf as a single theorem, by searching for Mathlib names instead of shapes. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 5 opened** (roadmap W3-1): the finite probability layer now has a home. A pre-integration space with `crealFinite` over `CReal.sumRange` and a Dirac space as instances, and **every detachable subset of a finite index set proved an integrable set** — the Petrakis–Zeuner base case, which is exactly this shelf. Five theorems new on ℝ land free on finite sums. The ℚ↔ℝ bridge to `Rat.expectation` did not land and is named as the next step. | `3d5320f68` |
| 2026-09-04 | **Next Five items 2 and 3 landed** (roadmap W1-10, W2-15; ADR-1616). The finite layer is stated once over `AlgS.OrderedRing`, 29 declarations, footprint 0, and **9 of the 11 ℚ theorems attempted are kernel-checked instances of the generic statement**, two more with a stated adjustment (the generic Markov is strictly stronger than the ℚ one, whose proof never used two of its hypotheses). Independence as `E[AB] ~ E[A]E[B]`, with independence ⇒ uncorrelated composing into the existing variance-of-a-sum theorem. The bridge to the integration space landed in the only form the carrier permits — the ℝ-valued expectation *is* the `crealFinite` integral definitionally, and the rational one is the integral across `ofRat` — because `IntSpace` is hard-wired to real values. Two known obstructions for the ~19 untried theorems: the indicator family needs a decidable order, not a record field; centred-vs-computational variance needs `mulComm` as an explicit hypothesis. | `86c7a1065`; `rat_prelude::` 287, `probability_s` 14 passed |
| 2026-09-05 | **The finite probability layer's L¹ metric exists** (roadmap W3-1 follow-on): `IntSpace.crealFiniteL1 n : Metric` with distance `∑ |X_i − Y_i|` pinned by `Eq.refl`. Convergence in L¹ is now a statement about a metric space rather than a hand-built bound, which is the shape the limit theorems want. | `a46e882b9` |
| 2026-09-05 | **Item 4 landed** (roadmap W3-12, ADR-1631): the Bernoulli model as a construction over the generic ordered ring with `IsDistribution` proved rather than assumed, mean and variance (the variance without commutativity), binomial mean and variance at ℚ from the sum theorems in two lines each, Chebyshev for the binomial in closed form, and a fourth-moment inequality. **Hoeffding did not land, and the reviewer's guess about why was wrong**: `exp` exists on ℝ; what is missing is any joint law — the shelf has no product space, which is also why independence had to be stated as `E[AB] ~ E[A]E[B]`. That is the next construction for this reviewer, ahead of measure theory. | `3e0ab5105`; `rat_prelude::binomial` 12, `probability` 14 passed in the lane |
| 2026-09-06 | **Item 4, second slice** (roadmap W3-12, ADR-1653): four-wise uncorrelatedness as a definition, the fourth central moment of a sum bounded by `Σ M₄ + 3(Σ σ²)²`, and the resulting tail bound — a `1/m²` concentration rate where Chebyshev gives `1/m`. This is the first Hoeffding-class rate the finite carrier can state without a joint law or `exp`. Hoeffding itself is still behind the product space. The ℚ prelude's build cost roughly doubled with this slice's ring expansions; sizing that is a named follow-up. | `b92194ec7`; `rat_prelude::` 313 passed in the lane |
| 2026-09-06 | **Re-measured against `main`, and the verdict changed.** Shelf: **74 axiom-free kernel declarations** — 54 at ℚ (8 definitions, 46 theorems) and 20 over `AlgS.OrderedRing` (7, 13) — against the "~30 theorems" this file carried, and **52 ledger facts, all `proved`**; counted per declaration, 50 of the 74
have their own fact and 9 of the 24 without one are theorems, not definitions. `IntSpace` measured at **98 declarations**, all derived and axiom-free, carrying a derived `measure`, a counting measure, a Dirac space and the L¹ metric family. **Two claims corrected.** (a) "No measure theory to build on" is false: a measure landed on 09-04 and it did *not* unlock the limit theorems — the blocker was misdiagnosed. (b) "The WLLN is proved" is true of the name and overstates the result: the kernel's own doc calls `Rat.weak_law_of_large_numbers` a renaming of the finite-sample Chebyshev bound "stated at each finite `m` rather than as a limit". **The product-space blocker verified, not repeated:** no `prod`/`joint`-named declaration in `Rat` (543), `AlgS` (390) or `IntSpace` (98) is a product space — the only hits are `Rat.prodRange`, the finite `∏` built for determinants, which is its own positive control and which makes the product *rule* writable though not derivable. `CReal.expFn_add` and any `log`/`ln` confirmed absent with `expFn` as the positive control. No probability or `IntSpace` work is in flight in any unmerged branch. `shape_search` freshness control: `Complex.holomorphic_pow` (main's newest kernel commit, `2758e7b18`) is in the index. The old "Next five" is retained with its states; a new five is stated below it. | `97ce06aff`; `--ns Rat` 543 / `--ns AlgS` 390 / `--include-constructed --ns IntSpace` 98 of 4,765; `count-landmark-facts.py` total=2954 proved=2678 |

## How to re-measure

The name grep this section used to carry was **broken and silently so**: the
prelude does not write `"Rat.expectation_add"` anywhere — names are interned
as `child(kernel, "expectation_add")` under a `Rat` root — so the grep matched
one string in an assertion message and returned a single line. Use the kernel
index instead.

```sh
# The ℚ shelf: 54 declarations (8 definitions, 46 theorems) at 97ce06aff.
S=target/release/examples/shape_search   # build once: cargo build --release --example shape_search
$S --ns Rat --limit 5000 | grep -E '^MATCH  Rat\.(IsDistribution|PairwiseUncorrelated|FourwiseUncorrelated|expectation|variance|covariance|indicator|markov|chebyshev|weak_law|bernoulli_law|binomial|fourth_moment|uniform_is_distribution|prob_|sumVars)'

# The generic layer: 20 declarations (7 definitions, 13 theorems).
$S --ns AlgS --limit 1000 | grep -E '^MATCH  AlgS\.OrderedRing\.(IsDistribution|Independent|expectation|variance|covariance|markov|bernoulli|uncorrelated_of_independent)'

# The integration space: 98 declarations. ~5 min — it builds the constructed preludes.
$S --include-constructed --ns IntSpace --limit 2000

# The product-space blocker, with its own positive control (prodRange must appear).
$S --ns Rat --limit 5000 | grep -iE '^MATCH  Rat\.[A-Za-z_.]*(prod|joint)'

# The ledger: 52 facts, every one `proved`.
python3 - <<'PY'
import json, glob, re
names = re.compile(r'Rat\.(expectation|variance|covariance|indicator|markov|chebyshev|weak_law'
                   r'|bernoulli_law|binomial|fourth_moment|Fourwise|Pairwise|IsDistribution|prob_)'
                   r'|AlgS\.OrderedRing\.(expectation|variance|covariance|markov|Independent'
                   r'|IsDistribution|bernoulli|uncorrelated)')
from collections import Counter
c = Counter()
for f in sorted(glob.glob('artifacts/facts/*.json')):
    d = json.load(open(f))
    if names.search(json.dumps(d)):
        c[d.get('epistemic_status')] += 1
        print(d.get('epistemic_status'), d.get('id'))
print(dict(c), sum(c.values()), 'facts')
PY
```

Before believing any ABSENT above, check that the binary is not stale: run
`$S --include-constructed --name-contains <a name from main's newest kernel
commit>` and confirm it is found.

## Related

- [03-classical-analysis.md](03-classical-analysis.md),
  [06-topology.md](06-topology.md) — the measure-theory chain
- [02-constructive-analysis.md](02-constructive-analysis.md) — the limit
  machinery convergence in probability needs
- [07-combinatorics.md](07-combinatorics.md) — the finite carriers underneath
