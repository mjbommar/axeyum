# 02 — Constructive analysis

Reviewer: a Bishop-school constructive analyst
Verdict, 2026-09-04: **excited, and the most favourable reviewer in the department**
Last measured: 2026-09-04 at `1856cdb3c`

> "Almost nobody builds this. You have a working constructive real line with
> integration on it and no choice anywhere. Where is the fundamental theorem
> of calculus?"

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

Their reservations are about reach rather than method. The fundamental theorem
of calculus is not there, which is startling given that both halves of it are
nearly in hand. And the transcendental functions are developed pointwise and
somewhat ad hoc — `cosOne` converges, π has bounds — rather than as a general
theory of power series with a radius of convergence.

## What they would say is missing

- **The fundamental theorem of calculus**, both directions. The single largest
  omission relative to what is already built.
- **A general power series theory.** Radius of convergence, term-by-term
  differentiation, and the standard functions defined *from* it rather than
  each by hand.
- **Uniform convergence as a first-class notion**, with the interchange
  theorems that make analysis composable.
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

- [ ] **1. The fundamental theorem of calculus.** Both directions, over the
      existing Riemann integral, with an explicit modulus. Their view: you are
      one theorem away from being able to say you have calculus, and you have
      not said it.
- [ ] **2. Power series with a radius of convergence**, and `exp`, `sin`, `cos`
      redefined from it with their functional equations derived rather than
      hand-proved. Consolidates the ad-hoc transcendental work into a theory.
- [ ] **3. Uniform convergence and the interchange theorems.** Limits with
      integrals, limits with derivatives. Without these, every analytic
      argument stays local and hand-built.
- [ ] **4. A constructive metric-space carrier**, with completeness and
      Bishop-style total boundedness, so that ℝ becomes an instance rather
      than the whole subject. The obvious second instance is `CPoint`, which
      already exists.
- [ ] **5. Differentiability on an interval, with the mean value theorem in
      its constructive form.** The MVT is classically an existence statement
      and constructively needs care; getting the right statement is itself the
      contribution, and it is what unlocks Taylor with remainder.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: 476 proved ℝ facts, zero open. Riemann integration, IVT by bisection, EVT, uniform continuity, suprema, exp/cos/π/sqrt, `CReal.orderedRingS`. No FTC. | ledger snapshot at `1856cdb3c` |

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
