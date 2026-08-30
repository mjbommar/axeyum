# ADR-0870: The D0 effort measurement refines, rather than confirms, "retrieval is the bottleneck" -- and finds a bigger, unnamed category

Status: accepted
Date: 2026-08-30
Index-summary: Classified 32 sampled completed/declined lane episodes into a
9-category taxonomy for the L3-D0 phase
(docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md); trust/
plumbing work (safety_evidence + integration + infrastructure_maintenance)
is 19/32 episodes against proof_assembly's 4/32, so D1-D4's order is revised
and D1's first pilot target is redirected from a mathematical declaration
subsystem to a repeatedly-decayed artifact/gate subsystem

## Context

The D0 exit criterion
(docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md) asks for at
least 20 representative completed/declined episodes, classified into a stable
taxonomy of {statement repair, missing definitions, retrieval, proof
assembly, kernel debugging, semantic falsification, safety evidence,
integration}, and explicitly says to **use the distribution to choose D1-D4
order rather than assuming proof search dominates**.

CLAUDE.md already carries a related but narrower claim, from
`docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`:
"more lane-hours went to re-deriving what existed than to proof difficulty",
resting on a **lane-reported tally of thirteen instances, explicitly marked
as not independently audited.** This ADR is that audit, not a restatement of
it.

## Method

Sampled 32 episodes from the day's `docs/plan/status/*.md` (123 new files)
and `docs/research/09-decisions/adr-08*.md` (52 new ADRs), deliberately for
coverage rather than randomly: completed and declined and partial; both
mathematical proof-production and infrastructural/safety work; fast wins and
multi-step diagnoses. Every episode's classification basis is recorded
(self-report vs. corroborated) and every "corroborated" claim is
independently re-verified by the gate itself -- a cited commit must resolve
via `git cat-file -e` in this repository's object store, a cited ADR must
have a matching file, a cited source file must exist. 28 of 32 episodes are
corroborated this way; 4 rest on self-report alone (named in
`artifacts/effort-taxonomy/report.md`).

Full taxonomy, episode set, generator, gate, and mutation-verified test suite
are at `artifacts/effort-taxonomy/` and `scripts/{gen,check}-effort-taxonomy.py`
(`just effort-taxonomy`).

## What the distribution shows

| category | count | share |
| --- | ---: | ---: |
| `safety_evidence` | 11 | 34% |
| `proof_assembly` | 4 | 12% |
| `integration` | 4 | 12% |
| `infrastructure_maintenance` (added, not a D0-named category) | 4 | 12% |
| `retrieval` | 3 | 9% |
| `kernel_debugging` | 3 | 9% |
| `statement_repair` | 1 | 3% |
| `missing_definitions` | 1 | 3% |
| `semantic_falsification` | 1 | 3% |

`infrastructure_maintenance` was added deliberately (justified in
`taxonomy.json`'s `category_additions`) rather than stretched into
`integration` or `safety_evidence`: repairing a gate that went red from a
merge, or a script archived out from under its own citations, is neither
first-time wiring nor new trust measurement -- it is reactive repair of
decay in something already trusted, and it recurred often enough in the
sample to need its own bucket.

Combined, `safety_evidence` + `integration` + `infrastructure_maintenance`
("trust and plumbing") account for **19 of 32 episodes (59%)** -- more than
the four categories the D1-D4 roadmap is explicitly aimed at
(`missing_definitions` + `retrieval` + `semantic_falsification` +
`proof_assembly`, 9/32, 28%) combined.

## Verdict on "retrieval is the bottleneck"

**Refined, not confirmed and not refuted.**

Within the 7 mathematical-domain episodes specifically (new theorems or
definitions, as opposed to ledger/gate/kernel-plumbing work), retrieval was a
major component -- primary or secondary -- in 4 of 7 (`already-proved-sweep`,
`nat-lcm-gcd`, `blocked-mirror-divergences`, `totient-mul`): each is a case
where checking what already existed changed how much new work was needed,
sometimes closing most of a target list without a single new proof term. That
is consistent with the design review's claim, on the population where the
claim was actually made.

It is not the dominant cost of "theorem effort" once the full sampled
population is considered, because a majority of today's episodes were not
proof production at all. The original claim was never measured against that
larger population, so it cannot be said to have predicted or covered it --
and a plurality of today's measured effort (59%) went somewhere the claim
does not mention.

A second, count-blind caveat: `semantic_falsification` is the rarest primary
category in this sample (1/32) but CLAUDE.md's own gotchas record several
near-misses in this exact area (a false coprimality-independence claim
verified numerically at only 2 of 26 relevant pairs, a vacuous
least-number-principle control, forgeable Pratt/CRT/monomial-bound
certificates) where the cost of NOT falsifying first was an entire family's
proof budget. Count-based distribution cannot see this; a rare category can
still carry the largest tail risk per instance.

## Decision

1. **Adopt the 9-category taxonomy** (the D0 spec's 8 plus
   `infrastructure_maintenance`) as the standing frame for future D0-style
   sampling; extend `artifacts/effort-taxonomy/episodes.json` rather than
   replacing it, so the sample compounds instead of resetting.

2. **Reorder D1-D4's near-term emphasis.** The roadmap's D1 (declarative
   declaration spec) -> D2 (structural retrieval index) -> D3
   (counterexample-first falsification) -> D4 (obstruction compiler)
   sequence is not overturned, but near-term investment is re-weighted:
   - **D3 stays first-priority.** It is already partially built
     (`l0-s3-semantic-controls`'s 13-fixture retained pack, ADR-0752) and its
     leverage per instance is high even at low frequency, per the caveat
     above.
   - **D2 (retrieval) is elevated ahead of further D1 mathematical-spec
     work**, because when retrieval friction occurs in a proof-production
     episode it is decisive (paragraph above), while `missing_definitions`
     -- the failure mode D1 is aimed at -- occurred only once in this sample
     and was handled cleanly by hand (`nat-dist-nth`) without needing
     generated scaffolding.
   - **D1's first pilot subsystem is redirected.** The roadmap says "start
     with one newly added small subsystem" without naming one. Given 59% of
     measured effort is trust/plumbing and several of those episodes are
     literally "a hand-maintained artifact's invariant broke because nothing
     re-derived it" (`284`, `285`, `328`, and `340`'s own finding that a
     statable-vocabulary row's constant list is the one field no gate
     re-derives), D1's declarative-spec-and-generated-surface mechanism is
     pointed first at a repeatedly-decayed **artifact/gate** subsystem
     rather than a purely mathematical declaration subsystem. This is the
     same mechanism the roadmap already specifies; only the pilot target
     changes.

3. **No new roadmap phase is added.** `infrastructure_maintenance`'s size is
   partly attributable to this specific week's ADR-0717 L0-L2 rollout
   (safety-matrix, statement-identity, semantic-control, kernel-differential,
   declaration-graph, graph-join phases all landed in the sampled window) and
   this 24-hour sample cannot distinguish a standing structural cost from a
   one-time program-startup cost. Re-measure after ADR-0717's L0-L2 phases
   settle before deciding whether a dedicated phase is warranted; extending
   D1's pilot target (decision 2) is the no-regret move available now.

## What would change this decision

A repeat of this sampling exercise (extend, do not replace,
`artifacts/effort-taxonomy/episodes.json`) after the ADR-0717 L0-L2 rollout
completes. If `infrastructure_maintenance`'s share falls sharply once that
program stabilizes, decision 3 is confirmed and no phase is needed. If it
stays comparable, that is the evidence for adding one.

## Non-decisions

This ADR does not change any fact's status, any gate's pass/fail semantics
outside of registering the new `effort-taxonomy` gate itself, or any
existing ADR's decision. It adds a measurement and a re-weighting of
near-term emphasis within the existing D1-D4 sequence.
