# Lane: topology-decision — W0-3 decided by building W2-1 and measuring

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, topology-decision, 2026-09-04).** Roadmap W0-3
(the constructive-topology design ADR) and W2-1 (a metric-space carrier with
ℝ and `CPoint` as instances). Both closed. Reviewer 06 goes from *zero
topology declarations* to 49.

**The decision, and how it was reached.** W0-3 asked which constructive
topology to adopt — open sets, apartness spaces, or locales. It was settled
the way [ADR-1595](../../research/09-decisions/adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md)
settled quotients on the same day: by **building the item that was supposed to
depend on the answer** and measuring what it actually needed.
[ADR-1602](../../research/09-decisions/adr-1602-the-metric-layer-first-then-pointfree-and-not-open-sets.md)
records the result. The metric carrier needed **no topology at all** — nothing
in the twelve-field record is a subset, so the constructive objection to
open sets never arose — and `Metric.Complete` generalizes
`CReal.converges_of_cauchy` off ℝ at a cost of **two already-landed bridge
lemmas and three `Exists.rec`s**. So the roadmap's `W2-1 → W0-3` dependency is
**measured false**. Recommendation: metric layer first (it carries W2-2, W2-3
and W2-10 alone), pointfree frames for topology proper when a non-metrizable
space is actually needed, open-set topological spaces never; apartness is not
a third option because a metric supplies it.

**What the next lane needs to know.**

- **`Metric` is in-tree and indexed.** `shape_search --include-constructed
  --ns Metric` returns `FOUND 49`. Both `shape_search` and
  `kernel_declaration_projection` were **blind to the new prelude** until this
  lane added a `metric` group to each — the same failure
  `kernel_declaration_projection`'s own `ipc` comment records. Any future
  prelude that sits on top of `cpoint` must be added to both or every
  retrieval query about it returns a confident, wrong ABSENT.
- **W2-2 (continuity) and W2-3 (Bishop compactness) are unblocked and need no
  decision.** Bishop compactness *is* total boundedness plus completeness, and
  `Metric.Complete` is landed.
- **W2-10 should be split.** The *product* metric is buildable today
  (`CReal.max` or `CReal.add` on the two distances; the triangle inequality
  follows from `max_le`/`add_le_add`). The *subspace* is blocked on `Subtype`,
  which this kernel does not have — verified case-sensitively with `Exists` as
  the positive control. Relativize with a predicate instead of carving a
  carrier, which is what `AlgS.Hom.ker`/`image` and every `…On` in `creal/`
  already do.
- **A stale blocker was corrected.** `CPointPrelude::cauchy_schwarz`'s doc says
  the unsquared norm form "is not expressible, let alone provable, here"
  because the kernel has `natSqrt` and no `CReal.sqrt`. `CReal.sqrt` and its
  toolkit landed afterwards; `Metric.CPoint.distTriangle` (Euclid I.20,
  unsquared) is the counterexample and it admitted on the first kernel run.
- **A concrete-numeral reduction probe on `CReal` is vacuous.** `CReal.zero`
  and `CReal.one` are closed terms that compute, so `|1−0|` and `|0−1|` whnf
  to the same rational and `Equiv.refl` proves the swapped statement. The
  first version of the probe had exactly this hole and its negative control
  caught it. Use symbolic arguments.

**Gates run.** `metric::` suite 17 passed / 0 failed in 64 s (`--release`,
`--test-threads=4`); `validate-facts.py` 2762 facts / 0 errors;
`check-links.sh` all links ok; both `validate-facts` control suites green
after the allowlist widening. Mutation table in ADR-1602 §6: four of five mutations kill EXACTLY one test each; the fifth (weakening a record FIELD) poisons the shared prelude build and kills all 17, which is reported as non-discriminating rather than as five-for-five.

<!-- plan-section: landed-changes -->

| 2026-09-04 | topology-decision | `Metric` carrier + ℝ instance + completeness generalized off `CReal.converges_of_cauchy` (`e43a8105c`) |
| 2026-09-04 | topology-decision | Euclidean plane instance with the UNSQUARED triangle inequality and unsquared Cauchy–Schwarz (`b34e2dbd7`) |
| 2026-09-04 | topology-decision | ADR-1602 closes W0-3; four curated facts; `shape_search` and `kernel_declaration_projection` taught to index the new prelude (`0e78494cc`) |
