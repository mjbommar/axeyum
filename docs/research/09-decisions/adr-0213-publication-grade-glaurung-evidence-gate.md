# ADR-0213: Publication-grade Glaurung evidence gate

Status: accepted
Date: 2026-07-17

## Context

Axeyum and Glaurung now have strong engineering evidence: byte-pinned query
streams, strict sort validation, original-term model replay, exact work and
finding identities, deterministic resource limits, repeated process-level
controls, RSS alarms, and explicit `Unknown` outcomes. Those gates have caught
real consumer soundness defects and have supported bounded product-policy and
optimization decisions.

The Glaurung pre-submission reviewer checklist identifies a different question:
what evidence is sufficient for a defensible paper performance claim? The
current evidence does not yet answer it. In particular, aggregate ratios can
mix different decided subsets and warm/fallback traffic; current comparisons do
not provide a topology-equivalent warm Z3 control; and shadow mode does not
establish finding parity when each backend drives exploration with its own
models. The existing coefficient-of-variation thresholds are regression alarms,
not statistical confidence intervals.

This decision closes the publication-evidence boundary without invalidating the
engineering admission gates or deprioritizing cold term-to-AIG-to-CNF work as a
product concern.

## Decision

Treat strict-typing correctness as the lead Axeyum/Glaurung contribution and
hold every new headline performance claim behind a separate publication-grade
evidence gate.

The critical gate is completed in this order:

1. Extend fixed-work ordered traces with stable per-check identity, both
   backend result classes and timings, and an explicit warm-versus-fallback
   classification. Run at least five identical-work repetitions. Report
   `{both-decided, z3-only, axeyum-only, neither}` separately; compute latency
   comparisons only over the paired both-decided population; report the
   geometric mean of per-query ratios with a deterministic bootstrap 95%
   confidence interval, per-backend p50/p90/p95/p99 and CDFs, and process-level
   coefficient of variation. Sweep the timeout without changing the fixed work.
2. Compare cold and warm Axeyum against topology-equivalent cold and warm Z3 on
   the same ordered stream, and add at least one neutral third-party backend.
   Process/FFI boundary cost is a separately named cell, never folded into a
   solver claim.
3. Run each backend as Glaurung's authority, compare stable finding and sink
   identities, and adopt a checked canonical model-selection policy if model
   choice changes exploration. Report parity before and after rather than
   treating verdict agreement in a Z3-led shadow stream as end-to-end parity.
4. Support the correctness claim with a stated TCB, measured end-to-end proof
   coverage, a standing well-typed multi-oracle differential fuzzer, and a
   regression corpus for the three consumer emission defects already found.

Contribution ablations, a neutral QF_BV corpus and second workload axis, honest
cold/warm-hit-rate reporting, and measured WASM/RSS/proof deployability follow
those critical items.

Existing exact-work, replay, finding, resource, RSS, and regression-variance
gates remain mandatory for product admission and optimization screening. They
do not substitute for paired publication statistics. Historical aggregate
ratios remain labeled descriptive or engineering-local; they are not promoted
to paper speedups retroactively.

GQ5 remains the leading pure-solver optimization lane because cold attribution
still selects bit blasting and CNF ahead of SAT. Its next candidate follows the
paired fixed-work harness so the same evidence machinery can evaluate it. This
is a sequencing change for evidence quality, not a claim that the cold
optimization problem disappeared.

## Evidence

- The reviewer checklist classifies baseline fairness, paired statistics,
  timeout/decided-population separation, and authoritative finding parity as
  critical acceptance blockers, and recommends implementing the paired
  fixed-work harness first.
- Existing ordered traces carry per-check backend timings but do not yet carry
  both backend result classes in a form sufficient to construct the four
  decided/nondecided buckets.
- Existing methodology explicitly labels the 3% time/ratio and 2% Z3-drift
  thresholds as regression alarms rather than significance claims.
- ADR-0206 and ADR-0207 demonstrate why result-class separation and strict
  typing are substantive: timeout splits must not be collapsed into verdict
  parity, and a declared-width defect silently changed Z3's bit placement.
- ADR-0212 demonstrates why fixed semantic work and timing stability must both
  hold: slower-core calibration changed actual bounded outcomes, while the
  ordinary-core no-op control failed the predeclared variance alarm.

## Alternatives

- Publish the existing ratios with caveats: rejected because caveats do not
  remove the one-shot-Z3, different-decided-population, or finding-parity
  confounds.
- Replace the existing engineering gates with conventional statistics:
  rejected because paired confidence intervals cannot detect changed query
  bytes, work, findings, replay failures, or lifecycle drift.
- Pause all solver optimization until the paper suite is complete: rejected.
  Product improvements remain valuable, but their aggregate screening numbers
  are not publication claims.
- Make correctness a supporting result and retain performance as the lead:
  rejected because the current strongest independently checkable result is the
  strict typed boundary that exposed three real consumer defects.

## Consequences

The immediate Glaurung/Axeyum work becomes measurement-schema and analysis
plumbing, followed by a warm Z3 control and authoritative finding parity. GQ5
resumes through that stronger harness. PLAN and STATUS must distinguish product
admission, optimization evidence, and paper evidence whenever they report a
ratio.

The paper narrative leads with strict types, actionable sort errors, replay,
and checked evidence. Performance remains a supporting result until the four
critical gates pass. If those gates narrow or eliminate the apparent warm win,
the result is reported as such rather than repaired by changing the population,
timeout, or baseline after inspection.
