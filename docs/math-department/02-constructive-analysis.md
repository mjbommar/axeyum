# 02 — Constructive analysis

Reviewer: a Bishop-school constructive analyst
Verdict, 2026-09-04: **excited, and the most favourable reviewer in the department**
Last measured: 2026-09-04 at `1856cdb3c`

> "Almost nobody builds this. You have a working constructive real line with
> integration on it and no choice anywhere. Where is the fundamental theorem
> of calculus?"
>
> **Answered 2026-09-04: it was already there, and the reviewer had missed it.**
> Both directions were admitted 2026-08-27, a week before this file was
> written.

**Correction, recorded 2026-09-04.** The first version of this review said the
fundamental theorem of calculus was missing and made it the reviewer's
number-one item. That was **false**. `CReal.hasDerivative_antiderivative`
(`1b91195d0`) and `CReal.integral_eq_antideriv_diff` (`d1bdae9e7`) were both
admitted on 2026-08-27, with empty axiom footprints and registered facts.

The cause was measured rather than guessed, and it is systemic: **307 of the
476 `CReal` facts (64%), and 1,054 of 2,764 ledger-wide (38%), carry
`gen-kernel-facts.py`'s mechanically-generated prose**, which opens by stating
that it deliberately makes no mathematical characterisation of the theorem.
The generator's refusal is correct and is part of why the ledger is
trustworthy. The defect is that nothing distinguishes *no prose has been
written* from *there is nothing here* — so the ledger answers "is X proved?"
and cannot answer "what do we have?", which is the question a review is built
from. ADR-1605 proposes the fix. Every other absence claim in this folder is
under audit for the same reason (`AUDIT-2026-09-04.md`).

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

## The persona

Works in the tradition of Bishop's *Foundations of Constructive Analysis*:
every existence claim carries a construction, every real number carries a
modulus, and the law of excluded middle is not available. Has spent a career
explaining that constructive analysis is not a restriction of classical
analysis but a different and more informative subject. Instinctively checks
two things in any formalization: whether countable choice was smuggled in, and
whether "not equal" was used where apartness was meant.

## What the library has today

**476 proved ℝ facts, zero open, all with empty axiom footprint.**

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
| differentiation | `hasDerivative_const` and the derivative apparatus |
| integration | Riemann sums with an interval-relative mesh: `riemannSumTotalEpsLe`, `riemannSumDeepCauchyFolded`, mesh refinement, splitting, additivity |
| transcendentals | `exp` with dominant-term bounds, `cosOneConverges`, π with `twoLePi` and the half-term bounds, `sqrt` with `sqrt_mul` |
| algebra of the line | `left_distrib`, `pow_le_pow_of_one_le`, `pow_nonneg`, `pow_le_one`, `eq_zero_of_mul_self_zero` |
| the theorems | intermediate value (`ivt_bisect_approx`, by bisection with an explicit modulus), extreme value |
| **the FTC, both directions** | `hasDerivative_antiderivative` and `integral_eq_antideriv_diff` (2026-08-27), plus `integral_by_parts`; and from 2026-09-04 the `_of_uc` forms that drop the redundant boundedness witness, since `bounded_of_uniformly_continuous` *computes* it from the continuity witness the caller already supplies |
| structure | `CReal.commRingS`, `CReal.orderedRingS`, `CReal.addGroupS` over the setoid algebra spine |

The IVT is proved the way this reviewer would want it proved: by bisection,
producing an approximate root to any requested precision, not by asserting a
classical existence.

## Their verdict

This is one of the more complete machine-checked constructive real analyses in
existence, and the reviewer would know, because the comparison set is small.
Three things earn their respect specifically:

**Apartness is data, not negation.** The library carries `apart` as a positive
witness and the setoid spine (`AlgS`) was built precisely so congruence
obligations are explicit fields rather than rewriting. That is the correct
design and it is the one most formalizations get wrong.

**No choice, anywhere.** The footprints are empty. Bishop's own development
uses countable choice freely and modern constructivists argue about whether it
should; a development that avoids it entirely is a stronger artifact than
Bishop's book.

**Integration exists.** Most constructive formalizations stop at continuity.
Riemann sums over an interval-relative mesh, with refinement and additivity
proved, is real work and it is the foundation everything analytic needs.

Their reservations are about reach rather than method. The transcendental
functions are developed pointwise and somewhat ad hoc — `cosOne` converges, π
has bounds — rather than as a general theory of power series with a radius of
convergence. (The FTC reservation in the first draft of this review was the
reviewer's own error, not the library's; see the correction above.)

## What they would say is missing

- ~~**A general power series theory.**~~ **[AUDIT] present** — a power-series
  layer landed 2026-08-27 (audit row A10); the verdict prose calling the
  transcendentals ad hoc was wrong.
- ~~**Uniform convergence as a first-class notion**, with the interchange
  theorems.~~ **[AUDIT] present**: `CReal.UniformConvergesOn` as a carrier,
  `uniform_limit_uniformly_continuous`, `hasDerivative_uniform_limit`, and
  `weierstrassMTest`, all 2026-08-27 (audit row A3).
- **Constructive metric spaces.** The line is complete; there is no notion of
  a complete metric space, so nothing generalizes off ℝ.
- **The Bishop compactness apparatus.** Total boundedness, located subsets,
  and uniform continuity on compact sets stated in the general form rather
  than on intervals.
- **Multivariate anything.** No ℝⁿ, no partial derivatives, no multiple
  integrals. The plane exists as `CPoint` but carries no calculus.

## The blocker

None of a fundamental kind, which is what makes this reviewer optimistic.
Everything on their list is reachable with the primitives the kernel already
has. Two practical constraints slow it:

**Build cost.** The ℝ prelude is 155,750 lines of Rust and its debug stack
requirement is 16 MiB; a single new deep declaration has repeatedly broken
unrelated tests. See
[prelude-build-cost.md](../contributor-guide/prelude-build-cost.md).

**Setoid overhead.** Every construction over ℝ must carry its congruence
obligation explicitly. The `AlgS` spine that landed 2026-09-03 was built to
make this systematic; before it, congruence was rediscovered per lemma.

## Next five, in their priority order

- [x] **1. The fundamental theorem of calculus.** ~~Both directions, over the
      existing Riemann integral, with an explicit modulus.~~ **Already proved
      2026-08-27; the item was the reviewer's error.** What did land on
      2026-09-04 is the pair of `_of_uc` forms with the redundant boundedness
      witness removed, and the finding that the constructive MVT is *not* a
      prerequisite: FTC-II routes through `constant_of_zero_deriv`, and the
      uniformity of the modulus replaces the MVT's asserted point.
- [x] **2. Power series with a radius of convergence** — *done 2026-09-05; the radius is data, and exp and cos are instances.* — **[AUDIT] a layer exists** (row A10); what remains is redefining `exp`/`sin`/`cos` *from* it. Original framing:, and `exp`, `sin`, `cos`
      redefined from it with their functional equations derived rather than
      hand-proved. Consolidates the ad-hoc transcendental work into a theory.
- [x] **3. Uniform convergence and the interchange theorems.** **[AUDIT]
      Already proved 2026-08-27**, including the Weierstrass M-test. Audit row
      A3.
- [ ] **4. A constructive metric-space carrier**, with completeness and
      Bishop-style total boundedness, so that ℝ becomes an instance rather
      than the whole subject. The obvious second instance is `CPoint`, which
      already exists.
- [x] **5. Differentiability on an interval, with the mean value theorem in
      its constructive form.** **[AUDIT] Already proved 2026-08-27**:
      `fermat_interiorExtremum`, `rolle_interiorExtremum`,
      `mvt_interiorExtremum`. Audit row A8. Original framing: The MVT is classically an existence statement
      and constructively needs care; getting the right statement is itself the
      contribution, and it is what unlocks Taylor with remainder.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: 476 proved ℝ facts, zero open. Riemann integration, IVT by bisection, EVT, uniform continuity, suprema, exp/cos/π/sqrt, `CReal.orderedRingS`. **Claimed no FTC — this was false.** | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Correction.** The FTC was proved 2026-08-27, before this file existed. Cause measured: 64% of `CReal` facts carry generated prose that makes no mathematical claim. Lane `ftc` added `hasDerivative_antiderivative_of_uc` and `integral_eq_antideriv_diff_of_uc` (arity 5 and 7, down from 7 and 9), each footprint 0, and established that the constructive MVT is not a prerequisite. `creal::` 230 passed. Next Five items 2–5 are **not** re-verified and are under audit. | `182d0dd7d`; ADR-1597 |
| 2026-09-04 | **A finding about this shelf from roadmap W3-1**: generalizing `CReal.integral` into an integration-space record re-derived only 1 of 6 interval theorems, because the theorems this reviewer admired — linearity, monotonicity, the absolute bound — are precisely the record's axioms, not its consequences. The `Integrable` predicate had to be `Sort 1` rather than `Prop`, since `UniformlyContinuousOn` is data whose modulus the integral consumes. And a stale blocker fell: `uniformly_continuous_abs` was written into the ADR as absent, then found derivable from `uniformly_continuous_max`/`_min` because `abs` is `max x (neg x)` by definition. | `3d5320f68` |
| 2026-09-05 | **Item 2 landed** (roadmap W2-5, ADR-1638): `CReal.powerSeriesPartial` converges inside a radius given as data (coefficient bound plus a ratio strictly below one), and `expSeriesPartial`/`cosSeriesPartial` are proved `Equiv` to the generic series at their coefficients — so the hand-built exp and cos shelves are now instances. The comparison, ratio and geometric tests were already here; the reviewer's audit row A10 undercounted them because `shape_search` does not index `creal`. Termwise sum and scalar multiple inside a common radius are the short residue. | `ed30eb7f9` |

## How to re-measure

```sh
python3 - <<'PY'
import json, glob, collections
c = collections.Counter()
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f))
    if (d.get('formal') or {}).get('fragment') == 'CReal': c[d.get('epistemic_status')] += 1
print(c)
PY

# the ℝ suite needs release + a deep stack
RUST_MIN_STACK=1073741824 scripts/cargo-serialized.sh test --release \
  -p axeyum-lean-kernel --lib -- creal:: --test-threads=4
```

## Related

- [03-classical-analysis.md](03-classical-analysis.md) — the same shelf, judged
  by someone who wants measure theory
- [04-algebra.md](04-algebra.md) — why ℝ is a setoid and not a quotient
- [diary-constructive-ivt.md](../mathematics-2026-08/diary-constructive-ivt.md),
  [diary-apart-as-data.md](../mathematics-2026-08/diary-apart-as-data.md)
