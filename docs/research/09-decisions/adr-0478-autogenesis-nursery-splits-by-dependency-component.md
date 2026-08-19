# ADR-0478: Autogenesis nursery evaluation splits by dependency component

Status: accepted
Date: 2026-08-18
Index-summary: Freeze nursery splits by declared dependency component, reserve proof-derived edges for admission credit, and exclude Autogenesis-1 from evaluation yield

## Context

Autogenesis-1 proves that one exact counterfactual Nat chain closes, but it is
not a generalization population. The current fact ledger has 110 facts and six
proof routes, yet only 23 direct proof-derived kernel edges across ten
consequents. Its useful Nat facts occupy one connected proof family, while the
genuinely open or conjectured facts have no registered proof route. A random
row split would therefore leak premises and proof shapes; a route-stratified
split would mostly select isolated facts and falsely suggest composition
coverage.

The next programme boundary must permit nursery authoring without granting an
authored dependency or intended route any truth authority.

## Decision

The v1 Autogenesis nursery is a separate manifest over fact-ledger statements.
Each entry records an explicit provenance class, theorem family, proof shape,
route hypotheses, answer-access policy, and one of four partitions:
`longitudinal`, `train`, `development`, or `held-out`.

Evaluation splits are frozen before target outcomes and use weakly connected
components of the authored `depends_on` graph. No component may cross train,
development, and held-out. Theorem families and proof shapes likewise cannot
cross evaluation partitions, and mutations remain beside their source fact.
These conservative split rules prevent a known premise chain or renamed proof
template from appearing on both sides even before its proofs exist.
Authored dependencies remain curriculum metadata: an admission may claim an
edge only when the accepted proof independently derives it. Route hypotheses
likewise grant no dispatch, checking, or admission authority.

`F:nat-zero-add -> F:nat-mul-one` is the exact longitudinal partition. It is
always excluded from autonomous yield and held-out gain. The initial manifest
is deliberately foundation-only; it must report not ready until it contains
100--300 evaluation facts, all three evaluation partitions, real declared
dependency depth, multiple provenance and route-hypothesis families, mutations,
and at least one held-out component.

## Evidence

The repository-derived chain catalog reports 23 direct proof-derived edges, ten
distinct consequents, maximum depth five, and fourteen named kernel facts not
covered by the dependency inventory. Direct ledger inspection reports nine
open or conjectured facts, none with a registered proof route, and only two
cross-route `depends_on` edges; neither is an independently derived
heterogeneous proof composition.

`scripts/check-autogenesis-nursery.py` makes the negative baseline executable.
It rejects component leakage, reuse of the Autogenesis-1 component, unknown
facts, dangling mutation controls, malformed classifications, and weakened
population floors. Its normal gate succeeds only when the report is internally
valid; `--require-ready` separately fails while the population is incomplete.

## Alternatives

- Random row splits were rejected because neighboring facts and proof templates
  leak across them.
- Splitting only by current proof route was rejected because route is absent for
  open facts and does not identify premise leakage.
- Reusing all settled kernel facts as held-out was rejected because their proof
  terms and outcomes shaped the current implementation.
- Waiting to define a split until after authoring was rejected because target
  outcomes would then influence evaluation membership.

## Consequences

- Nursery authors can work independently after assigning whole dependency
  components to a frozen partition.
- The initial readiness result is honestly red; it is infrastructure, not a
  Phase 3 result.
- A declared chain can drive scheduling and leakage control but cannot earn
  compounding credit until accepted evidence derives the dependency.
- Future imported Mathlib statements may supply provenance-classified source
  material without vendoring Mathlib or treating imported proofs as autonomous
  Axeyum proofs.
