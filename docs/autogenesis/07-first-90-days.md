# First 90 days: Autogenesis-1

## Objective

Deliver the smallest credible demonstration that Axeyum's verified reasoning
capacity compounds:

> Under fixed inputs and budgets, automatically prove and admit B, observe that
> B unlocks A, then automatically prove and admit A. Reproduce the complete
> sequence in a clean environment with zero proof-affecting human intervention
> and zero unaccounted assumptions.

This schedule is a planning envelope, not a calendar promise. Phase exit gates,
not elapsed days, control progression.

## Explicit non-goals

The first programme does not include:

- model training or LLM integration;
- generated conjectures;
- automatic code modification;
- distributed execution;
- a new solver backend;
- broad SMT-LIB product completion;
- full Lean import or workflow parity;
- a general tactic language; or
- claims of mathematical novelty.

If the selected chain exposes a real solver or certification blocker, repair the
smallest reusable blocker and retry; do not broaden the programme silently.

## Sprint 0 — Freeze the experiment

### Tasks

- **S0.1** Run and retain the AG0 baseline at an exact clean commit.
- **S0.2** Select candidate B -> A chains from Nat/Int whose statements and
  dependencies are independently reviewed.
- **S0.3** Require at least one negative statement-strength mutation per fact.
- **S0.4** Measure B and A independently through current routes; A must depend on
  B semantically, not merely through authored metadata.
- **S0.5** Choose one primary chain and one fallback before implementing the
  orchestrator.
- **S0.6** Write the ADR for episode identity, evidence bundle, and transaction
  boundary.

### Exit

The exact chain, counterfactual, budgets, proof route, checker, expected
dependency, and corruption controls are preregistered. No target outcome has
been hidden after observation.

## Sprint 1 — Episode and snapshot

### Tasks

- **S1.1** Define internal v1 Rust/Python representation for goal snapshot and
  episode; defer public schema until exercised.
- **S1.2** Content-digest statement, dependencies, library, route configuration,
  and resource policy.
- **S1.3** Add typed outcomes for solved, declined, invalid evidence,
  operational failure, and timeout/resource exhaustion.
- **S1.4** Serialize append-only attempt records with deterministic ordering.
- **S1.5** Repeat one no-op/decline episode twice and compare bytes.
- **S1.6** Add truncation, unknown-field, version, digest, and duplicate-ID
  rejection tests.

### Exit

An episode can represent a current successful and failed route without losing
identity, assurance, or resource information.

## Sprint 2 — Typed evidence handoff

### Tasks

- **S2.1** Adapt exactly one proof-producing route to emit the route-neutral
  evidence bundle.
- **S2.2** Reparse the goal and evidence in a fresh arena/process.
- **S2.3** Derive checker command/operation from registered evidence type rather
  than accept arbitrary caller-authored shell text.
- **S2.4** Bind every transformation and reduction map to content digests.
- **S2.5** Record explicit trust steps and reject assurance inflation.
- **S2.6** Corrupt producer IDs, statement bytes, evidence bytes, and footprint;
  each control must reject.

### Exit

The same evidence is accepted independently of producer-local arena identity,
and no caller-authored label can upgrade its assurance.

## Sprint 3 — Transactional autonomous closure

### Tasks

- **S3.1** Select B from a machine-readable frontier snapshot.
- **S3.2** Dispatch it under the preregistered budget.
- **S3.3** Build the proposed fact delta from checked typed artifacts.
- **S3.4** Derive proof route, dependencies, and footprint where supported.
- **S3.5** Stage, validate, and atomically apply or revert the transition.
- **S3.6** Re-run in a clean process using only committed inputs and staged
  artifacts.
- **S3.7** Confirm the manual closer still refuses missing/invalid evidence.

### Exit

B closes automatically and reproducibly. This is Phase 1 completion, not yet
Autogenesis-1.

## Sprint 4 — Counterfactual snapshot and scheduler

### Tasks

- **S4.1** Materialize the existing proof-derived kernel chains as candidate
  curricula; do not duplicate their retained proofs into the runnable snapshot.
- **S4.2** Define a counterfactual overlay that withholds B, A, and their proof
  terms while leaving the authoritative ledger unchanged.
- **S4.3** Freeze the primary chain, fallback, mutations, and pre-B snapshot.
- **S4.4** Implement deterministic scoring from readiness, route feasibility,
  cost, unlock count, diversity, and gate coupling.
- **S4.5** Ensure an accepted transition, not a mere solver result, triggers
  readiness recomputation.
- **S4.6** Record why each eligible fact was or was not selected.

### Exit

The scheduler produces a deterministic ranked queue over a content-identified
pre-B snapshot, and the snapshot cannot retrieve the retained B or A proof. A
larger nursery is subsequent evaluation infrastructure, not a prerequisite to
the first two-step closure.

## Sprint 5 — Two-step compounding

### Tasks

- **S5.1** Launch from the preregistered pre-B snapshot.
- **S5.2** Select, solve, check, admit, and record B.
- **S5.3** Derive that A is newly ready and schedule it without human override.
- **S5.4** Make B available through the admitted library/plan context.
- **S5.5** Solve, check, admit, and record A.
- **S5.6** Replay A against the pre-B snapshot and retain the expected failure.
- **S5.7** Repeat the entire sequence from a clean checkout.
- **S5.8** Audit intervention logs, trusted-base delta, and byte determinism.

### Exit

Autogenesis-1 passes exactly as defined in the programme README.

## Sprint 6 — Harden and publish the result

### Tasks

- **S6.1** Run focused tests, full feature tests, Clippy, docs, link checks, fact
  validation, plan generation, and the complete repository gate where the host
  is capable.
- **S6.2** Mutation-test the credited chain, selection, replay, and autonomous
  intervention count.
- **S6.3** Produce a retained result note with exact commit, inputs, artifacts,
  resource use, failures, and limitations.
- **S6.4** Generate the first acquisition-funnel report.
- **S6.5** Add the next live work item only from the measured failure
  distribution; do not preselect Phase 3 implementation.
- **S6.6** Update the owned plan lane and regenerate root `PLAN.md`.

### Exit

The result is integrated, reproducible, honestly bounded, and usable as the
baseline for Phase 3 proof-plan design.

## Candidate chain selection criteria

The primary B -> A chain should:

- require a real theorem dependency that the kernel can derive;
- fit current axiom-free Nat/Int library support;
- use a currently certifiable/reconstructable route;
- complete under a deterministic modest budget;
- have a meaningful statement-strength mutation;
- not be a load-bearing negative control for another gate;
- fail or exceed budget without B for a stable, understood reason;
- avoid a chain whose proof is already hard-coded into the orchestrator; and
- be understandable enough for independent manual review of intent.

Do not choose a famous theorem for spectacle. Choose the chain that most cleanly
tests the architecture.

## Deliverables

| Deliverable | Durable location, to be fixed by ADR |
|---|---|
| Autogenesis baseline | generated report under `docs/plan/generated/` |
| Episode and goal snapshot | content-addressed retained artifact |
| Evidence bundle | retained evidence directory |
| Nursery facts | `artifacts/facts/` or a schema-separated nursery source |
| Held-out split manifest | committed immutable manifest |
| Orchestrator and replay commands | `scripts/` prototype, then exercised Rust boundary if warranted |
| Acquisition-funnel report | generated report plus machine-readable source |
| Final result | dated durable result note under `docs/plan/` |

Exact paths are an ADR outcome because introducing new public artifact schemas
or a crate before exercising the boundary would violate the project's normal
sequencing.

## Stop conditions

Stop and repair before proceeding if:

- a wrong verdict or accepted corruption appears;
- evidence succeeds only in the producer arena;
- a checker/gate cannot be made to fail on its control;
- the selected chain requires a hidden human proof;
- dependency on B is merely handwritten rather than proof-derived;
- a retry is credited without a new accepted knowledge state;
- the clean replay needs uncommitted or network-fetched state;
- the full trusted-base delta cannot be enumerated; or
- current root `PLAN.md` authorizes a conflicting higher-priority P0 repair.

## Decision after Autogenesis-1

Do not automatically proceed to learned models. Inspect the episode population:

- If most failures are missing composition, begin Phase 3 proof plans.
- If most are missing evidence, prioritize proof-production and reconstruction.
- If most are missing premises, deepen DAG/library coverage and retrieval.
- If most are solver limitations, route the top reusable blocker into the
  existing solver programme.
- If the nursery is too easy or too artificial, improve the population before
  optimizing the policy.
- If orchestration cost dominates, address identity, caching, and replay
  performance before scaling lanes.

The point of the first 90 days is not to confirm the roadmap. It is to make the
system produce enough evidence to rewrite the roadmap intelligently.
