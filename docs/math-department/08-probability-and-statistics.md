# 08 — Probability and statistics

Reviewer: a probabilist, with a statistician looking over their shoulder
Verdict, 2026-09-04: **a real finite-probability shelf, and no measure theory to build on**
Last measured: 2026-09-04 at `1856cdb3c`

> "You have Markov, Chebyshev, and the variance of a sample mean under
> pairwise uncorrelatedness. That is the weak law of large numbers, minus the
> limit. Why did nobody tell me this was here?"

**Correction, recorded on creation.** The first pass of this review said the
library contained "one item, a Cauchy-Schwarz inequality over the rationals."
That was wrong, and it was wrong because the reviewer searched for
`probability_space` and `random_variable` — Mathlib's names — rather than for
the shape. The measured count is about 30 proved theorems. This is the exact
failure mode the contributor guide warns about: *search for the step, not the
name*, and an empty result from a tool never pointed at your subject is
indistinguishable from a strong negative.

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

**A finite/discrete probability theory over ℚ, roughly 30 proved theorems, all
axiom-free.** A random variable is a rational-valued function on a finite
index range; expectation is a normalized `sumRange`.

| layer | theorems |
|---|---|
| expectation | `expectation_add` (linearity), `expectation_const`, `expectation_smul`, `expectation_sumVars`, `expectation_le`, nonnegativity |
| indicators | `indicator_nonneg`, `indicator_le`, `expectation_indicator_le_one`, `variance_indicator`, `variance_indicator_le_quarter` |
| variance | `variance_eq` (the computational formula), `variance_smul`, `variance_add_eq`, `variance_add_of_uncorrelated`, `variance_sumVars`, `variance_scaled_mean`, `variance_scaled_add_nonneg`, nonnegativity |
| covariance | symmetry, `covariance_add_right`, `covariance_smul_left`, `covariance_sumVars`, `covariance_sumVars_left` (bilinearity) |
| inequalities | `Rat.markov_inequality`, Chebyshev over ℚ, Cauchy–Schwarz for covariance in all three cases (positive variance, zero variance, general) |
| the good one | `variance_sampleMean_uncorrelated` and **Chebyshev's inequality for the sample mean of pairwise-uncorrelated random variables** |

The last row is the substantive result: it is the concentration bound that
makes the weak law of large numbers work, stated for pairwise (not full)
independence, which is the sharp hypothesis.

## Their verdict

**The statistician is pleased and slightly startled.** Bilinear covariance,
the variance of a sum under uncorrelatedness, Markov and Chebyshev, and a
concentration bound on the sample mean is a coherent, correctly-chosen core.
Everything an introductory mathematical-statistics course proves in its first
third is here, over an exact rational carrier with no floating point and no
assumed axioms. For finite-sample statistics — which is most of what is
actually computed in practice — this is usable today.

**The probabilist is unsatisfied for a structural reason.** There is no
probability *space*: no σ-algebra, no measure, no notion of an event beyond an
index range, and no random variable as a measurable function. So none of the
following can even be stated:

- any limit theorem — no weak law (the limit is missing, not the bound), no
  strong law, no central limit theorem
- continuous distributions, densities, or the normal distribution
- independence as a property of σ-algebras rather than an uncorrelatedness
  hypothesis carried by hand
- conditional expectation, filtrations, martingales, stochastic processes

Their assessment: this is a *combinatorial* probability library that has been
built as far as it can go without measure theory, and it has been built well.
Everything above it is behind the same door.

## What they would say is missing

- **Measure theory.** σ-algebras, measures, the Lebesgue integral. See
  [03-classical-analysis.md](03-classical-analysis.md).
- **The limit theorems.** ~~WLLN~~, SLLN, CLT. **[AUDIT] The WLLN is proved**
  (`Rat.weak_law_of_large_numbers`, 2026-08-24). The strong law and the
  central limit theorem are confirmed absent.
- **Independence proper**, and the relationship between independence,
  uncorrelatedness, and the existing hypotheses.
- **Named distributions.** Bernoulli and binomial are within reach over the
  finite carrier; the normal needs measure and the Gaussian integral.
- **Statistical inference.** Estimators, bias, consistency, confidence
  intervals, hypothesis tests — all of which need the limit theorems.
- **Entropy and information theory**, which needs logarithms on ℝ connected to
  the finite carrier.

## The blocker

**Two, and they are different sizes.**

The near one: **the weak law of large numbers needs a limit, not a measure.**
Convergence in probability of the sample mean is a statement about a sequence
of rational-valued bounds tending to zero, and `CReal`'s convergence apparatus
can express that. This is reachable now and would be the first genuine limit
theorem in the library.

The far one: **everything else needs measure theory**, which needs topology,
which needs a design decision. See [06-topology.md](06-topology.md) and
[03-classical-analysis.md](03-classical-analysis.md). Constructive measure
theory is additionally awkward, so this is not a transcription job.

There is also a carrier question worth settling early: the finite probability
layer lives on ℚ and the limits will live on ℝ. Bridging them means either
lifting the finite theory to `CReal` or proving a transfer result. The
`AlgS.OrderedRing` spine now covers both carriers, which makes a generic
statement of Markov and Chebyshev plausible.

## Next five, in their priority order

- [x] **1. The weak law of large numbers.** **[AUDIT] Already proved:
      `Rat.weak_law_of_large_numbers`, landed `54592604a` on 2026-08-24, ten
      days before this review claimed it was one limit away.** The reviewer's
      error, not the library's; see the audit row A2.
- [ ] **2. Generalize the finite probability layer over `AlgS.OrderedRing`**,
      so expectation, variance, Markov and Chebyshev hold over ℚ and ℝ at
      once. Prerequisite for (1) being stated cleanly rather than bridged by
      hand.
- [ ] **3. Independence as a definition**, with the theorem that independence
      implies uncorrelatedness, so the existing hypotheses are recognizable to
      a reader from the field.
- [ ] **4. ~~Bernoulli~~ and binomial distributions** over the finite carrier,
      with mean and variance, and Hoeffding's inequality if it is reachable.
      **[AUDIT] Bernoulli is present** (audit row A11); the binomial
      distribution and Hoeffding are confirmed absent.
- [ ] **5. Measure and the Lebesgue integral**, once
      [06-topology.md](06-topology.md) and
      [03-classical-analysis.md](03-classical-analysis.md) settle their design
      decisions. Everything the probabilist wants is behind this and nothing
      before it is wasted.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: ~30 proved finite-probability theorems over ℚ — expectation, indicators, variance, covariance, Markov, Chebyshev, sample-mean concentration under pairwise uncorrelatedness. No measure theory, no limit theorems. **Correction:** the first review pass under-reported this shelf as a single theorem, by searching for Mathlib names instead of shapes. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 5 opened** (roadmap W3-1): the finite probability layer now has a home. A pre-integration space with `crealFinite` over `CReal.sumRange` and a Dirac space as instances, and **every detachable subset of a finite index set proved an integrable set** — the Petrakis–Zeuner base case, which is exactly this shelf. Five theorems new on ℝ land free on finite sums. The ℚ↔ℝ bridge to `Rat.expectation` did not land and is named as the next step. | `3d5320f68` |

## How to re-measure

```sh
python3 - <<'PY'
import json, glob, re
pat = re.compile(r'probab|expect|varian|covarian|random|Chebyshev|indicator|Markov|sample mean', re.I)
n = 0
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f)); t = d.get('title') or ''
    if pat.search(t): n += 1; print(d.get('epistemic_status'), t[:90])
print(n, 'facts')
PY

grep -rhoE '"Rat\.(expectation|variance|covariance|indicator|markov)[A-Za-z_]*"' \
  crates/axeyum-lean-kernel/src/ | tr -d '"' | sort -u
```

## Related

- [03-classical-analysis.md](03-classical-analysis.md),
  [06-topology.md](06-topology.md) — the measure-theory chain
- [02-constructive-analysis.md](02-constructive-analysis.md) — the limit
  machinery the WLLN needs
- [07-combinatorics.md](07-combinatorics.md) — the finite carriers underneath
