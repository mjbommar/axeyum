# Metrics and evaluation

## The primary question

The programme asks:

> How much additional independently verified problem-solving capacity did the
> system acquire, at what human, compute, and trust cost?

Commit count, theorem count, solver decision rate, and generated-candidate
volume are diagnostics. None is the primary outcome.

## Acquisition funnel

Every run reports counts and transition rates for one exact population:

| Stage | Meaning |
|---|---|
| Eligible | Dependencies and domain preconditions are satisfied |
| Selected | Scheduler offered the goal under the run policy |
| Planned | At least one statically valid proof plan or route attempt exists |
| Attempted | Execution began under a registered budget |
| Decided | A route produced the required semantic outcome |
| Evidence-produced | Portable evidence exists for the outcome |
| Independently checked | A checker re-derived the evidence in its own context |
| Reconstructed | A complete kernel term or equivalent accepted artifact exists |
| Admitted | Kernel or domain acceptance boundary accepted it |
| Recorded | A valid knowledge transition was staged and replayed |
| Autonomous | No human wrote, repaired, or selected the credited proof after launch |
| Compounding | Admission made another credited goal newly reachable or cheaper |

Report both absolute counts and conditional conversion rates. A high admission
rate after manually selecting three easy goals is not high autonomous yield.

## Core metrics

### Autonomous verified yield

```text
autonomously recorded facts / eligible facts
```

Always pair it with population identity, assurance floor, compute budget, and
time window.

### Capability gain

A vector, not a single count:

- newly reachable held-out facts;
- newly accepted evidence families;
- reduction in median or tail cost at equal assurance;
- increase in proof-plan or domain diversity;
- dependencies or descendants unlocked;
- decrease in human interventions; and
- change in trusted assumptions or checker coverage.

### Compounding coefficient

For each admitted result, count useful downstream changes:

```text
newly ready descendants
+ previously failed descendants now solved
+ proof plans shortened by reuse
```

Keep these components separate. A fact becoming “ready” does not mean it was
solved.

### Human intervention

Record at least:

- target selection override;
- formal-statement edit;
- premise hint;
- route or plan override;
- proof repair;
- evidence-row edit;
- checker or gate repair;
- budget override; and
- novelty classification.

An episode with any proof-affecting intervention is useful but not autonomous.

### Trust cost

Track:

- new axioms;
- new trusted reductions or proof rules;
- unverified evidence rows;
- structural attestations versus reasoning proofs;
- checker lines and dependency changes;
- native/unsafe dependencies; and
- acceptance-policy relaxations.

A gain purchased by weakening the assurance floor is reported as a trade, not
an improvement.

## Evaluation populations

Use several non-substitutable populations:

| Population | Purpose |
|---|---|
| Nursery train/dev | Rapid iteration and debugging |
| Nursery held-out chains | Compounding and novel-premise evaluation |
| Adversarial mutations | Soundness, statement strength, and identity |
| Existing regression corpora | Solver no-loss and route correctness |
| External formal benchmarks | Generalization and ecosystem comparison |
| Domain-held-out tasks | Adapter validity and epistemic classification |
| Longitudinal replay set | Forgetting and reproducibility over releases |

Random theorem splits are insufficient. Split by dependency component, theorem
family, generator template, proof-plan shape, and premise novelty so near
duplicates do not turn memorization into apparent reasoning.

## Causal evaluation of a capability change

For every claimed capability acquisition:

1. Freeze exact pre-change episodes and held-out goals.
2. Preregister the blocker class and expected affected subset.
3. Run multiple repetitions where timing sensitivity matters.
4. Land the smallest intervention.
5. Re-run identical inputs, budgets, seeds, and assurance floors.
6. Report gained, retained, lost, flipped, timed-out, and invalid-evidence rows.
7. Re-run held-out populations not used to design the intervention.
8. Attribute only changes matching the preregistered mechanism.
9. Preserve rejected or zero-gain results.

Net score is never enough. One wrong verdict cannot be offset by ten new
decisions.

## Learned-policy evaluation

A learned policy receives credit only when:

- it beats deterministic and simple retrieval/search baselines;
- compute and wall-time budgets are matched;
- the test population was frozen before training;
- data and premise leakage checks pass;
- accepted proofs survive with the policy absent;
- failures and invalid proposals are counted; and
- stability on earlier domains is reported.

Useful policy metrics include premise recall, valid-plan rate, node expansion,
time to first accepted proof, unique held-out facts solved, and expected verified
yield per compute unit.

## Conjecture evaluation

Generated conjectures pass a funnel of their own:

```text
generated
-> parses and type-checks
-> non-vacuous under mutations
-> not immediately refuted
-> not a normalized duplicate
-> near a useful capability frontier
-> established or informative counterexample
-> externally classified for novelty
```

Report every denominator. “Ten discoveries” without the generated and filtered
population is not an interpretable result.

## Dashboard contract

The eventual generated dashboard should show, for one exact revision:

- phase and authoritative exit status;
- acquisition funnel;
- DAG shape and nursery split;
- autonomous and human-assisted yield;
- proof/evidence assurance distribution;
- structured decline distribution;
- top blocker clusters by expected unlock value;
- compute and latency distributions;
- trusted-base delta;
- held-out policy comparison;
- longitudinal forgetting/regression; and
- artifact provenance and replay command.

Every headline needs a negative control or cross-check that can make it fail.

## Initial floors and non-goals

The first phases should use floors rather than ambitious production targets:

- Phase 1: one independently replayed closure, zero corruptions accepted;
- Phase 2: one two-step chain, zero proof-affecting human interventions;
- Phase 3: one held-out multi-route proof, zero unrecorded dependencies;
- Phase 4: one demand-selected capability with zero retained verdict loss;
- Phase 5: statistically and practically positive held-out gain at matched cost;
- Phase 6: one generated candidate that survives all classification gates.

Do not set a “theorems per day” target until autonomous utilization and failure
distribution have been measured over a sustained window.
