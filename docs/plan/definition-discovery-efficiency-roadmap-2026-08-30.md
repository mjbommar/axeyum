# Definition and proof discovery efficiency roadmap

Status: accepted programme under ADR-0717
Date: 2026-08-30

## Outcome

Move effort from theorem-specific Rust assembly into reusable mathematical
interfaces and proof producers.  Discovery remains untrusted and fast; one
small checker path decides durable credit.

## Current bottlenecks

- prelude builders still combine name registries, declaration fields, build
  order, helper construction, and dispatch;
- a target often becomes statable only after a lane discovers a missing
  datatype, finite-collection abstraction, congruence regime, or transport
  lemma by failing deep in a proof;
- retrieval is split among authored fact edges, kernel dependencies, lexical
  similarity, and isolated source exports;
- many `declare_*` paths encode one proof instead of a reusable strategy;
- false statements and vacuous formulations can consume proof effort before
  cheap computational checks run;
- proof bodies are Rust code, which is robust but verbose for exploration and
  expensive to compare structurally.

## Target architecture

```text
declarative declaration spec
  -> generated names/signatures/accessors/bindings/renderings/tests
  -> content-addressed environment

goal + proof-isolated graph + obstruction profile
  -> counterexample-first triage
  -> structural retrieval
  -> bounded reusable producers
  -> candidate kernel term
  -> theorem-credit safety contract
  -> atomic fact transition
```

Python may propose specs, rankings, skeletons, witnesses, and terms.  It cannot
relax checking or write proved status.  Rust remains the implementation and
admission boundary for durable declarations.

## Phases and exits

### D0 — Measure where theorem effort goes

Instrument lanes without capturing prompts or secrets.  Classify time/tool
steps into statement repair, missing definitions, retrieval, proof assembly,
kernel debugging, semantic falsification, safety evidence, and integration.

**Exit:** at least 20 representative completed/declined episodes with a stable
taxonomy; use the distribution to choose D1–D4 order rather than assuming proof
search dominates.

### D1 — Declarative declaration specification

Define a versioned typed specification for names, universes, binders,
definitions, equations, public theorem signatures, dependencies, and build
phase.  Generate repetitive Rust accessors, Python types, Lean rendering
metadata, inventory registration, and basic equation/mutation tests.

Start with one newly added small subsystem; do not mechanically rewrite the
whole library.

**Exit:** generated and hand-built environments have identical declaration
identity/order/type/value digests for the pilot; duplicate names, missing
phases, and dependency cycles fail before kernel construction.  The pilot
reduces hand-maintained registration surfaces without enlarging the TCB.

### D2 — Structural theorem and proof index

Index Axeyum theorems by normalized type shape, head relations, binders,
definitions used, theorem dependencies, recursors, rewrite direction, and
proof skeleton.  Join proof-isolated Mathlib goal features without exposing
upstream proof values.

**Exit:** fixed queries reproduce exact ranked candidates; held-out facts are
excluded before feature construction; identity, structural, and lexical
signals are reported separately.

### D3 — Counterexample-first definition review

Every proposed public definition gets executable equations, non-degenerate
witnesses, and comparisons against an independent reference on a bounded
domain where possible.  Every theorem proposal runs the S3 falsification stage
before proof planning.

**Exit:** the retained false-statement corpus is found before producer dispatch;
definition mutations alter at least one reference observation; unexecutable
definitions carry an explicit review obligation.

### D4 — Obstruction-to-producer compiler

Normalize typed declines into the smallest missing capability: congruence,
rewriting under a relation, equality transport, implication introduction,
existential witness synthesis, induction motive, finite permutation,
inequality normalization, setoid congruence, or another registered class.
Cluster demand across facts and families.  A producer contract declares its
shape, budget, candidate inputs, negative controls, and target population.

**Exit:** each new producer is evaluated on multiple preregistered targets and
false controls; production provenance's multi-target counter moves; a
single-target producer is labeled a capsule and cannot justify generality.

### D5 — Bounded proof-plan IR

Introduce a small inspectable proof-plan representation above raw `ExprId`
construction: apply, exact, rewrite, symmetry, transitivity, constructor,
eliminate, induction, witness, and checked computation.  Compile it to ordinary
kernel terms; do not teach the kernel the plan language.

**Exit:** the compiler's output is byte/digest deterministic, plans render for
review, all terms are rechecked from scratch, malformed plans decline, and at
least three existing proof families become shorter without changing theorem
identities or footprints.

### D6 — Closed-loop batch discovery

For each graph-selected cluster:

1. materialize proof-isolated goals;
2. falsify statements;
3. retrieve exact candidates;
4. run bounded producers;
5. admit through the safety contract;
6. refresh graph/obstruction metrics;
7. select again from new durable state.

**Exit:** at least one batch establishes a theorem whose checked proof consumes
a theorem established by an earlier batch—not merely a scheduling dependency—
with no human-written target proof and an empty footprint.

## Ease-of-use deliverables

- `axeyum graph why <fact>`: explains priority, blockers, and downstream gain;
- `axeyum theorem triage <fact>`: statement identity, representability,
  counterexamples, and candidate producers;
- `axeyum theorem attempt <fact> --no-write`: deterministic bounded episode;
- `just check-theorem <fact>`: universal assurance and optional atomic credit;
- generated HTML/Markdown dashboards for graph frontier, obstructions, safety
  coverage, and production leverage.

Every command has stable JSON output, typed declines, explicit budgets, and
nonzero subject counts.

## Parallel ownership

For 2–3 simultaneous agents:

- schema/code-generation lane owns declarative specs and generated surfaces;
- retrieval/producer lane owns structural indexing and bounded proof plans;
- batch/evaluation lane owns immutable populations, falsification, metrics, and
  comparison—not producer implementation.

One writer owns each generated artifact key.  Lanes communicate through sealed
receipts rather than editing shared registries or counts.
