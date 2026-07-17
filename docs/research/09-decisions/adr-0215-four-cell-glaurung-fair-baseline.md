# ADR-0215: Four-cell Glaurung fair baseline

Status: accepted
Date: 2026-07-17

## Context

ADR-0214 makes the historical cold-Z3/warm-Axeyum population statistically
auditable, but does not remove ADR-0213's baseline confound. A fresh native Z3
solver and a retained Axeyum lineage differ in both solver and session
topology. The reviewer checklist correctly treats that comparison as
insufficient for a solver-performance claim.

## Decision

Accept Glaurung's off-by-default four-cell fair-shadow producer and the
additive `glaurung-ordered-check-measurement-v2` consumer contract.

For every cold-Z3-authoritative ordered check, the producer independently
times:

- Z3 cold one-shot;
- Z3 retained direct lineage;
- Axeyum cold one-shot; and
- Axeyum retained direct lineage.

The two retained cells use the same explorer source owner, serial sibling
lease, exact source-prefix ancestry, root-scope transitions, and temporary
assumption partition. Cell order rotates deterministically by occurrence. The
v1 `z3_*` and `axeyum_*` fields remain exact aliases for cold Z3 and warm
Axeyum, respectively; they are not silently reinterpreted.

Extend `scripts/analyze-glaurung-paired-traces.py` without invalidating v1. For
v2, require all four positive timings, outcomes, closed warm execution classes,
and stable fixed-work identities. Report four separate paired populations:
cold Z3/Axeyum, warm Z3/Axeyum, Z3 cold/warm, and Axeyum cold/warm. Each
population independently includes only occurrences decided by both named cells
in every repetition and uses ADR-0214's per-occurrence geometric mean,
deterministic bootstrap interval, latency quantiles, and per-run CV. Preserve
the historical cold-Z3/warm-Axeyum primary field for artifact continuity, but
do not present it as the fair comparison.

## Evidence

Glaurung's real incremental-Z3 tests cover retained model lifting, push/pop,
temporary assumptions, restoration, and exact source-identity sibling rewind
across cloned expression pools. Its v2 validator checks all four cells, total
timing, closed execution classes, authoritative cold-Z3 outcome, and v1 aliases.

Axeyum's paired-analyzer suite constructs five fixed-work v2 repetitions and
checks exact cold-backend, warm-backend, Z3 incremental, and Axeyum incremental
ratios. All ten analyzer tests pass, including v1 compatibility, four-cell CDF
generation, cross-repetition decided-outcome drift rejection, and the prior
fail-closed drift/error gates.

A real DptfDevGen smoke first published and validated 227 four-cell checks.
The clean repeated exercise then used Glaurung `4ae96cf`, five sequential
fresh processes, and a predeclared 60-second solver bound. Every repetition
preserves the same 561 checks; all four cells decide every occurrence with zero
operational result, disagreement, replay failure, or fallback. Both warm
populations contain seven created sessions and 554 retained checks.

The paired geomeans are 0.9661x [0.8709, 1.0706] for Z3/Axeyum cold and
0.7875x [0.6893, 0.8977] for Z3/Axeyum warm. Thus the fair warm result favors
Z3 on this driver; Axeyum is about 1.27x slower. The same topology improves Z3
8.9752x [8.5511, 9.4112] and Axeyum 7.3157x [6.4477, 8.2741] relative to their
cold cells. Per-run geomean CV is below 1.67% in every comparison. The exact
report and four-cell CDF are committed under
[`bench-results/glaurung-four-cell-dptf-20260717/`](../../../bench-results/glaurung-four-cell-dptf-20260717/README.md).

## Alternatives

- Compare retained Axeyum only with fresh Z3: rejected as the original
  confound.
- Use a persistent Z3 context but a fresh solver per check: rejected because it
  removes only context creation, not lineage reuse.
- Let Z3 use complete snapshots while Axeyum consumes deltas: rejected because
  the topology remains different.
- Pool all four cells into one headline ratio: rejected because it hides which
  mechanism moved.
- Replace v1 fields in place: rejected because it would change historical
  artifact meaning.

## Consequences

ADR-0213's topology-equivalent warm-Z3 mechanism and first clean N>=5
fixed-work control are complete. The fair result must replace, not decorate,
the historical cold-Z3/warm-Axeyum headline. The neutral third-party solver,
timeout-sensitive marked driver,
authoritative finding parity/canonical model policy, and multi-oracle assurance
remain open. This diagnostic does not change Axeyum's product-path admission or
default policy.
