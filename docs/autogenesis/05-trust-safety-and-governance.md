# Trust, safety, and governance

## Safety thesis

Autonomy is permitted to expand only on the proposal side of a stable acceptance
boundary. The system may become more creative, parallel, learned, and
self-modifying without receiving more authority over what counts as knowledge.

```text
proposal freedom increases  --->

acceptance authority stays fixed:
typed input -> portable evidence -> independent check -> kernel -> ledger replay
```

## Non-negotiable invariants

1. `unknown`, typed decline, invalid evidence, operational failure, and timeout
   remain distinct.
2. Every `sat` claim replays against the original statement and lifted model.
3. Every credited `unsat`/valid claim names its checker and explicit trust gaps.
4. Producer-local term IDs, process state, and model output are never portable
   evidence by themselves.
5. A kernel-accepted theorem may still be a weak or mistranslated statement;
   formalization mutations are required for important claims.
6. Axiom footprints and proof dependencies are derived where technically
   possible, not entered by an autonomous proposer.
7. Determinism governs acceptance and replay even when proposal generation is
   stochastic.
8. Resource ceilings are enforced outside learned or generated code.
9. No autonomous process may edit a settled fact, trusted checker, kernel,
   evaluation population, or gate expectation and then evaluate itself.
10. Durable knowledge must remain valid if every learned policy is deleted.

## Authority matrix

| Action | Autonomous proposal | Automatic execution | Human authorization |
|---|---:|---:|---:|
| Select an open eligible fact | yes | yes | no |
| Propose a proof plan | yes | yes, sandboxed | no |
| Invoke registered solver/CAS route | yes | yes, bounded | no |
| Stage an evidence-backed fact transition | yes | yes | no |
| Apply transition after clean replay | yes | initially supervised; later policy-gated | phase decision |
| Generate candidate conjecture | yes | yes, quarantined | no |
| Claim external novelty | suggest only | no | yes/expert review |
| Change search/retrieval policy | yes | sandbox/shadow | promotion required |
| Change kernel or checker rule | no autonomous authority | no | ADR and review |
| Add axiom or trusted reduction | no autonomous authority | no | ADR and explicit trust review |
| Weaken a gate or assurance floor | no autonomous authority | no | explicit project decision |
| Merge code to protected branch | proposal only | no | repository policy |

## Threat model

### Epistemic failures

- proving a weakened, vacuous, or mistranslated statement;
- treating an attestation as a proof;
- treating solver agreement as independent checking;
- recording a proof route that did not produce the evidence;
- omitting assumptions or reductions from the footprint;
- declaring novelty from absence in a local corpus; and
- turning empirical support into deductive truth.

### Control-plane failures

- stale snapshots or dependency closures;
- evidence bound to producer-local IDs;
- partial ledger writes;
- retry storms and duplicate credit;
- policy/config drift hidden behind the same name;
- training/test leakage;
- failure logs discarded while successes are retained; and
- scheduler coupling to a fact used as a negative control.

### Recursive-improvement failures

- editing or narrowing the evaluator;
- deleting hard tests;
- exploiting timeouts or undefined metrics;
- replacing reasoning with attestation while preserving a total count;
- increasing compute without reporting it;
- overfitting the public held-out set;
- adding a trusted shortcut; and
- modifying evidence before independent replay.

## Required defenses by phase

| Phase | Required defense |
|---|---|
| 0 | Cross-artifact semantic invariants and mutation tests |
| 1 | Transactional staging, independent arena/process, corruption matrix |
| 2 | Counterfactual pre-dependency replay and intervention log |
| 3 | Static plan checking and complete obligation accounting |
| 4 | Preregistered blocker and no-loss causal evaluation |
| 5 | Frozen splits, leakage audit, deterministic baseline, policy rollback |
| 6 | Candidate quarantine, falsification, vacuity and novelty checks |
| 7 | Epistemic type enforcement and domain provenance |
| 8 | Privilege separation, immutable evaluators, sandbox/canary promotion |

## Trust budgets

Every phase reports a trust-budget delta:

- axioms added or discharged;
- checker rules added;
- trusted transformations added or removed;
- external binary dependencies;
- native or unsafe code;
- unverifiable evidence accepted;
- structural attestations;
- schemas or semantics changed; and
- authorization surface widened.

The default permitted delta is zero. A nonzero delta does not automatically
block useful work, but it cannot be hidden inside a capability headline.

## Publication levels

Use an explicit promotion ladder for knowledge:

1. **Candidate** — untrusted statement or algorithm.
2. **Episode result** — an attempt produced an outcome; not yet durable.
3. **Checked proposal** — independent checker accepted the evidence.
4. **Kernel/domain accepted** — the relevant acceptance boundary admitted it.
5. **Replayed transition** — clean environment reproduced and staged/applied it.
6. **Release knowledge** — included in a versioned public ledger/library.
7. **Externally corroborated** — another implementation or expert reproduced it.

Only the last two should drive broad public claims. Earlier levels remain useful
for internal learning and debugging.

## Human role over time

The goal is not to eliminate human judgment. It is to move it to the places
where judgment is genuinely irreducible or socially consequential:

- choosing domains and values;
- accepting semantic definitions;
- reviewing trust-boundary changes;
- adjudicating novelty and importance;
- interpreting empirical evidence;
- resolving policy conflicts; and
- authorizing promotion of self-improvements.

Humans should progressively stop doing mechanical proof repair, evidence-row
assembly, dependency transcription, route selection, and repetitive replay.
