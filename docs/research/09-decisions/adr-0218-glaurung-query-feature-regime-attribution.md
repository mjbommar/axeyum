# ADR-0218: Glaurung query-feature regime attribution

Status: accepted
Date: 2026-07-17

## Context

ADR-0217 establishes a workload-dependent fair regime but deliberately leaves
its cause open. The initial hypothesis—small formulas dominated by FFI entry
cost favor Axeyum, while hard formulas favor Z3—does not fit the cold results:
IntcSST and SurfacePen favor Axeyum cold as well as warm, and vwififlt favors
Z3 cold.

The accepted traces already contain hash-verified canonical queries plus
outcome, consumer purpose, active constraints, exact-query identity, and warm
execution class. Those fields can narrow the hypothesis without modifying or
rerunning the producer.

## Decision

Accept a fail-closed query-feature attribution layer over the four committed
N=5 reports. Revalidate every referenced trace and query hash, retain the exact
fixed-work occurrence as the unit, and join paired cold/warm ratios to:

- SAT/UNSAT outcome and consumer purpose;
- warm-created versus warm-retained execution;
- active-constraint and exact-query occurrence counts; and
- bounded lexical SMT-LIB size, depth, declaration, assertion, width, and
  operator-family counts.

Report per-driver strata, within-driver Spearman correlations against log
paired ratio, tie-preserving pooled quantile bins, and marginal outcome/purpose
standardization. Label every correlation and reweighting as descriptive. Do
not use this four-driver observational sample to fit or publish a causal
classifier.

## Evidence

The analyzer ingests 20 validated traces and emits 9,526 occurrence rows. Its
recomputed driver ratios exactly match the accepted reports. Focused tests
cover lexical extraction, tied ranks, reverse rank correlation, complete
quantile partitioning, and the rule that equal feature values never split
across bins. The existing paired-analyzer suite remains green after making
purpose and active-constraint fields explicit on its internal check record.

The descriptive result is sharper than formula size:

- every driver favors Axeyum on SAT occurrences: 1.1634x--1.7693x warm;
- UNSAT ranges from 0.3324x on Dptf and 0.7887x on vwififlt to 0.9707x on
  IntcSST and 2.0382x on SurfacePen;
- retained-only warm ratios remain 1.4763x/1.4883x on IntcSST/SurfacePen,
  0.9937x on vwififlt, and 0.7552x on Dptf;
- address concretization favors Axeyum on every driver, while value witness
  favors Z3 on three of four; and
- exact-query frequency correlates positively with warm Axeyum advantage
  within every driver (+0.32 to +0.63 Spearman).

Median query bytes are 4,833 IntcSST, 6,138 Dptf, 18,924 SurfacePen, and 27,534
vwififlt. Larger queries correlate negatively with the warm ratio within all
four drivers, but that ordering cannot explain a small winning IntcSST, a
larger winning SurfacePen, a mid-size losing Dptf, and the largest parity
driver.

Marginal reweighting confirms composition is material. Standardizing to the
pooled SAT/UNSAT mix moves Dptf from 0.7875x to 0.9884x; standardizing to the
pooled purpose mix moves it to 1.1529x. These estimates lack confidence
intervals and the strata remain mutually confounded, so they are hypothesis
selection evidence rather than counterfactual claims.

The exact joined table and report are committed under
[`bench-results/glaurung-four-cell-regime-features-20260717/`](../../../bench-results/glaurung-four-cell-regime-features-20260717/README.md).

## Alternatives

- Name formula byte size as the boundary: rejected by the cross-driver order.
- Attribute the result solely to warm session creation: rejected because the
  IntcSST and SurfacePen advantages remain in thousands of retained checks.
- Pool all occurrences and publish a single feature correlation: rejected
  because driver composition visibly confounds pooled ranks.
- Treat marginal standardization as causal adjustment: rejected because
  outcome, purpose, shape, and reuse are not independently assigned.
- Rerun before using fields already committed in the trace: rejected as
  unnecessary evidence churn; the join is independently validated.

## Consequences

The paper may describe the winning regime as outcome-, purpose-, and
reuse-sensitive, with exact named strata. It may not yet say why those strata
favor one solver internally.

The next producer increment is per-check rewrite/AIG/CNF/SAT work and timing
for both cold and retained Axeyum, followed by matched-stratum comparison and a
neutral solver. This replaces generic formula-size speculation with a concrete
mechanism test. Authoritative finding parity and multi-oracle fuzzing remain
separate publication blockers.
