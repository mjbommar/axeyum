# Target architecture

## Architectural thesis

Autogenesis separates a rapidly changing **proposal plane** from a deliberately
small **acceptance plane**.

```text
UNTRUSTED PROPOSAL PLANE

  goal source -> scheduler -> retriever -> proof planner -> route portfolio
       ^                                                    |
       |                                                    v
  conjecturer <- capability learner <- structured episodes and declines

                              || typed artifacts only
                              \/

TRUSTED ACCEPTANCE PLANE

  parser/identity -> evidence checker -> reconstruction checker -> kernel
         |                  |                    |              |
         +------------------+--------------------+--------------+
                                    |
                                    v
                         transactional ledger proposal
                                    |
                                    v
                            clean-room replay gate
```

The proposal plane may use heuristics, LLMs, reinforcement learning,
evolutionary search, external solvers, speculative rewrites, and enormous
parallel search. None of it receives authority merely because it is capable.

The acceptance plane checks specific artifacts under explicit semantics and
budgets. It does not judge whether an idea is elegant or likely; it judges
whether the claimed transition follows under the named assumptions.

## Core objects

### 1. Goal snapshot

A goal snapshot freezes what was offered to the system:

- fact or candidate ID;
- exact formal statement and parser version;
- concept and domain references;
- dependency closure with content digests;
- available theorem/library digest;
- allowed routes and assurance floor;
- resource budget, seed, and determinism profile; and
- external/novelty status if known.

It must be possible to prove that a later replay saw the same problem.

### 2. Reasoning episode

A reasoning episode is an append-only record of an attempt, not a claim of
truth. Suggested v1 shape:

```text
Episode
  identity
    schema version
    episode id
    goal snapshot digest
    parent episode / retry cause
  policy
    scheduler version
    planner version
    route policy
    model identity, if any
  proposals[]
    proof-plan candidate
    score and rationale features
  attempts[]
    plan node
    input/output digests
    budget consumed
    typed outcome
    produced artifacts
  result
    solved | refuted | declined | operational-failure
    evidence bundle digest
    kernel term digest
  acceptance
    independent checks
    axiom footprint
    derived dependencies
    proposed fact delta
  impact
    newly ready descendants
    capability classification
```

Episodes must record failed attempts, superseded proposals, and budget stops.
They must never be rewritten into success after the fact.

### 3. Proof-plan IR

The proof-plan IR is a typed orchestration language above solver evidence and
below unconstrained natural-language plans. Its initial instruction families
should be deliberately small:

| Family | Initial instructions | Output obligation |
|---|---|---|
| Context | `introduce`, `assume`, `specialize` | Typed local context |
| Structure | `split_conjunction`, `split_cases`, `by_contradiction` | Child goals plus composition rule |
| Equality | `rewrite`, `normalize`, `substitute` | Equality evidence and rewritten goal |
| Library | `retrieve`, `apply_theorem` | Exact theorem identity and unification result |
| Quantifiers | `instantiate`, `skolemize_checked` | Portable binding/position record |
| Induction | `induct_nat` | Base and step goals plus kernel recursor skeleton |
| Engines | `dispatch_solver`, `dispatch_cas`, `enumerate_finite` | Typed result and evidence bundle |
| Composition | `close_subgoal`, `compose` | Complete proof object or explicit open obligations |

Every instruction has:

- a versioned syntax;
- static preconditions;
- deterministic operational semantics where possible;
- an explicit resource cost;
- a checker or a reconstruction rule;
- a declared effect on the local context; and
- a fail-closed decline outcome.

Proof-plan execution may be untrusted. A plan receives credit only when the
composed proof is accepted by an independent checker or the kernel.

### 4. Evidence bundle

The evidence bundle is the route-neutral handoff between search and acceptance.
It binds:

- original goal digest;
- transformed obligation digests;
- every reduction map;
- solver/CAS artifacts;
- proof-plan composition data;
- checker identities and versions;
- trust steps and assumptions; and
- final claimed outcome.

Raw in-process IDs are forbidden unless the independent checker reconstructs
and verifies their meaning in its own arena. Recent fresh-arena evidence bugs
make this a phase-1 invariant, not a later portability enhancement.

### 5. Capability record

A capability is not merely a supported logic name. It is a measured mapping:

```text
(goal features, context features, budget, assurance floor)
    -> distribution of typed outcomes
```

Capability records connect episodes to planning. They identify which reusable
mechanism would convert the largest set of valuable declines, and whether a
change actually improved held-out autonomous yield.

### 6. Knowledge transition

A knowledge transition is a proposed change from an open/candidate proposition
to a durable status. It carries:

- before and after fact bytes;
- episode and evidence bundle digests;
- checker observations;
- kernel declaration identity when applicable;
- derived dependency and axiom footprints;
- novelty/importance status kept separate from correctness; and
- newly ready descendants.

The transition is staged first. A separate replay process applies it only after
re-deriving the evidence in a clean environment.

## State machines

### Attempt state

```text
selected -> snapshotted -> planned -> executing
    -> solved -> checked -> reconstructed -> admitted -> proposed -> replayed
    -> declined
    -> operational-failure
    -> invalid-evidence
```

`declined`, `operational-failure`, and `invalid-evidence` are distinct. A
timeout is not evidence that a route is unsupported; invalid evidence is not an
ordinary unknown; a checker crash is not a refutation.

### Candidate state

```text
generated -> typed -> deduplicated -> triaged
    -> refuted
    -> proof-attempted -> established
    -> empirical-only
    -> assumption-bearing
    -> novelty-review
    -> rejected-formalization
```

Formal establishment, empirical support, and novelty never collapse into one
status.

## Bottom-up integration with present crates

The first implementation should prove boundaries before adding crates. A new
crate is justified only when two or more existing consumers exercise the
boundary, consistent with ADR-0001.

Likely initial placement:

- goal snapshots and route-neutral episode types near `axeyum-query` or in an
  internal module of the first orchestrator;
- proof-plan terms near `axeyum-query`, with execution adapters in
  `axeyum-solver`, `axeyum-cas`, and reconstruction;
- portable evidence bundle extensions alongside existing solver evidence;
- scripts for prototype selection, orchestration, and clean replay;
- JSON schemas under `artifacts/ontology/` only after the prototype reveals the
  exercised boundary; and
- a dedicated crate only after Rust API and command-line consumers both use the
  same episode/plan types.

This ordering avoids creating an `axeyum-agent` shell with no semantic center.

## Top-down domain model

The same architecture must eventually represent different epistemic products:

| Product | Acceptance condition |
|---|---|
| Mathematical theorem | Kernel-checked proof under explicit axioms |
| Finite computational claim | Reproducible computation plus checked bound/coverage |
| Solver verdict | Original-model replay or independently checked refutation |
| Program invariant | Semantics-bound obligation plus checked proof/counterexample |
| Rule/policy conclusion | Versioned rule semantics, facts, and derivation |
| Empirical hypothesis | Provenance and statistical evidence; never relabeled theorem |
| Algorithmic improvement | Immutable evaluator, correctness proof/tests, held-out gain |

The fact ledger may remain proposition-oriented. A future knowledge layer can
reference facts, claims, observations, policies, and experiments without
forcing them into one ontology.

## Over-the-horizon constraints

Choices made in early phases must preserve:

- dependent or richer binders beyond current first-order terms;
- proof plans whose steps are not all tactics or all solver calls;
- multiple kernels and external checkers;
- distributed search with content-addressed artifacts;
- nondeterministic proposal generation but deterministic acceptance replay;
- learned policies that can be replaced without migrating knowledge;
- scientific evidence that is not deductive proof;
- private-domain inputs with public, self-contained evidence where possible;
- explicit temporal and versioned knowledge; and
- safe evaluation of proposed changes to untrusted search code.

The stable interfaces should therefore be semantic artifacts and digests, not
model prompts, process IDs, temporary term handles, or one backend's trace.
