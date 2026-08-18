# Workstreams and sequencing

## Two views of the same programme

A top-down programme asks what complete system must exist. A bottom-up
programme asks which present boundary can be exercised safely next. Either view
alone fails:

- top-down-only work produces schemas, agent diagrams, and ambitious horizons
  with no executable semantic path;
- bottom-up-only work produces more routes, lemmas, and checkers without proving
  that knowledge acquisition compounds.

Autogenesis uses **meet-in-the-middle sequencing**. Every wave contains one
vertical product milestone and the smallest foundation increments it pulls.

## Top-down workstreams

| Workstream | Owns | Does not own |
|---|---|---|
| T1. Knowledge objective | Value, domain purpose, candidate lifecycle, novelty | Solver implementation |
| T2. Autonomous control | Episodes, scheduler, planner, retry, acquisition loop | Truth acceptance |
| T3. Evaluation | Autonomous funnel, held-out populations, causal attribution | Feature marketing |
| T4. Governance | Authority boundaries, promotion, rollback, trust budgets | Search heuristics |

## Bottom-up workstreams

| Workstream | Owns | Existing anchors |
|---|---|---|
| B1. Identity and artifacts | Digests, schemas, portability, transactional storage | fact schema, evidence artifacts, generated reports |
| B2. Proof composition | Plan typing, obligations, reconstruction, kernel admission | query IR, solver evidence, reconstruction, Lean kernel |
| B3. Search portfolio | Solvers, CAS, rewriting, quantifiers, induction, enumeration | solver/CAS/rewrite crates |
| B4. Knowledge graph | Fact dependencies, concept mapping, nursery, unlock calculation | fact ledger, concept DAG, dependency inventory |
| B5. Measurement and runtime | Budgets, determinism, traces, clean replay, distributed execution | benchmark harness, route trace, resource contracts |

## Cross-view dependency matrix

| Top-down need | Required bottom-up capability | First phase exercised |
|---|---|---|
| Durable autonomous attempt | B1 identity + B5 replay | 0-1 |
| Compounding knowledge | B4 connected nursery + B2 admission | 2 |
| General decomposition | B2 proof plans + B3 adapters | 3 |
| Capability investment | B5 typed declines + B4 unlock values | 4 |
| Learned improvement | B1 episode corpus + B5 frozen evaluation | 5 |
| Conjecture discovery | B4 candidate graph + B3 falsification | 6 |
| Domain expansion | B1 epistemic artifacts + B2/B3 adapters | 7 |
| Recursive improvement | B5 immutable evaluators + T4 authority | 8 |

## Critical path

```text
AG0 baseline
   |
   v
AG1 episode + evidence bundle + replay transaction
   |
   v
AG2 nursery + scheduler + admission-triggered retry
   |
   +--------------------------+
   v                          v
Autogenesis-1           AG3 proof-plan IR
                              |
                              v
                    AG4 structured capability acquisition
                              |
                              v
                    AG5 learned search policies
                              |
                              v
                    AG6 candidate generation
                              |
                              v
                    AG7 domain adapters
                              |
                              v
                    AG8 governed self-improvement
```

The first three phases are deliberately serial at their semantic boundaries.
Parallel implementation may occur within a phase only after artifact ownership
and interfaces are frozen.

## Pull protocol for existing roadmap work

The Autogenesis loop does not supersede existing solver and proof priorities by
fiat. It supplies a repeatable way to pull them:

1. Select an eligible, valuable goal from a committed population.
2. Run the current portfolio under a registered budget.
3. Retain the episode and classify the minimal stable blocker.
4. Group equivalent blockers across goals.
5. Estimate verified unlock value and implementation cost.
6. Choose the smallest reusable intervention.
7. Route it into the appropriate existing track and ADR process.
8. Re-run the exact pre-change episodes plus held-out controls.
9. Credit the change only for new independently accepted transitions.

Examples:

- nonlinear induction steps pull a QF_NIA mechanism or lemma, not “more
  induction”;
- an unportable certificate pulls evidence identity repair, not solver breadth;
- repeated missing premises pull retrieval or library connectivity;
- a proof-plan explosion may pull a representation change before a faster
  backend;
- a textual-session decline pulls A8/A10 work only when an actual consumer or
  domain adapter needs that surface.

## Wave plan

### Wave A — Truthful composition

Phases 0-1. One owner controls the transaction seam. Parallel lanes may audit
identity, select fixtures, and build controls, but there is one writer for the
episode/evidence contract until replay works.

Exit: a single automatic closure.

### Wave B — Compounding substrate

Phase 2. Parallel lanes may author independent nursery topics after the schema,
dependency rules, and held-out split are frozen. A separate evaluation lane
owns scheduler metrics and may not author target solutions.

Exit: Autogenesis-1.

### Wave C — Compositional intelligence

Phase 3. Proof-plan core, engine adapters, retrieval, and plan search can proceed
in parallel behind a stable plan typing contract. Kernel composition remains
single-owner until at least two adapters exercise it.

Exit: a held-out multi-route theorem.

### Wave D — Capability flywheel

Phase 4. Decline taxonomy, unlock analysis, and one solver/library capability
increment run as separate lanes. The evaluator owns the pre/post population and
does not tune the implementation.

Exit: demand-selected capability acquisition.

### Wave E — Adaptive and generative search

Phases 5-6. Dataset/evaluation work precedes model choice. Learned retrieval,
plan generation, self-play, and evolutionary search are replaceable proposal
policies.

Exit: held-out learning gain, then one honestly classified generated discovery.

### Wave F — Domain and recursive expansion

Phases 7-8. Domain adapters proceed independently only after the epistemic type
contract is fixed. Recursive-improvement proposals remain restricted to
untrusted policy surfaces.

Exit: two domain loops, then one safely promoted policy improvement.

## Parallel ownership guidance

When multiple lanes execute this programme, prefer ownership by semantic
artifact rather than broad feature name:

| Lane | Example owned paths/artifacts |
|---|---|
| Episode/identity | episode schema/types, digest rules, serialization tests |
| Acceptance/replay | evidence bundle verification, clean replay command |
| Nursery/DAG | authored nursery facts and dependency fixtures |
| Scheduler/evaluation | selection policy, held-out splits, metrics |
| Proof-plan core | plan syntax/type checker/composition rules |
| Engine adapter | one route adapter and its fixtures |
| Capability analysis | decline taxonomy and unlock report |

Shared generated files remain integration-owner outputs. Existing dirty
frontier artifacts are volatile benchmark output and must not be swept into an
Autogenesis change.

## Sequencing heuristics

Use these rules when evidence changes the queue:

1. Wrong verdict, invalid evidence, data loss, and ineffective gates preempt all
   phases.
2. A missing semantic contract precedes a performance optimization across that
   contract.
3. A portable artifact precedes distributed execution or learning from it.
4. Deterministic baselines precede learned policies.
5. Authored connected curricula precede generated conjecture curricula.
6. Falsification precedes expensive proof search on generated candidates.
7. Clean replay precedes automatic ledger mutation.
8. One demonstrated consumer precedes an abstraction; two precede a new crate.
9. Held-out evaluation is frozen before the implementation sees its answers.
10. Trusted-base changes always leave the autonomous authority boundary.

## What may proceed early

Research and fixtures may look ahead without claiming phase completion:

- collect candidate proof-plan operations from existing reconstruction routes;
- preserve richer route traces needed for future episodes;
- design nursery facts while Phase 1 is implemented;
- build decline examples and mutation controls;
- study retrieval and planning methods offline;
- prototype domain adapters without publishing conclusions; and
- catalogue self-improvement threat models.

This is how the programme keeps the horizon visible without letting horizon
gravity bypass current exit gates.
