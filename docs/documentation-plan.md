# Documentation Plan

Status: active roadmap
Last updated: 2026-08-07

The beginner sequence is now complete, and the user guide has live pages for
installation/build profiles, first SMT-LIB and Rust use, models/replay, UNSAT
evidence, limitations, benchmarks, corpus manifests, and a clean-environment
validated WASM/browser workflow. The contributor guide now has executable task
pages for setup, testing, operators, rewrites, solver routes, proof/evidence,
and benchmark artifacts. The internals sequence now documents the live IR,
evaluation, rewriting, lowering, SAT, dispatch, evidence, and Lean boundaries.
Every workspace crate now has a README, and the core public crates have
compile-tested rustdoc examples. The stable reference section routes public
API/configuration questions, catalogs all 203 checked-in Cargo examples with
their feature/tool and mutation boundaries, and indexes golden-tested/generated
logic, support, trust, and SMT-LIB protocol authorities without copying their
volatile tables. The short public project-state page now copies the latest weak
arithmetic rows from the append-only parity ledger, and the parity-doc gate
checks those rows against the ledger to prevent another stale snapshot.
The live indexes in [`docs/README.md`](README.md),
[`learn/README.md`](learn/README.md),
[`user-guide/README.md`](user-guide/README.md), and
[`reference/README.md`](reference/README.md) are authoritative for the public
guide. The consumer-application front door now routes the property SDK, EVM
bug-hunter, and bounded Rust verifier to their current crate contracts and
48-case aggregate measurement, while labeling the per-app plans and status
files as historical journals. The curriculum, review, plan, and research
archives now have explicit front doors that separate current authorities from
dated records. The prover-track front door now makes the same distinction:
substantial Lean-kernel prerequisites are built, while the CIC/IR bridge and
native goal/hole/tactic layer remain planned rather than shipped.

This plan describes how to reshape Axeyum's public documentation so it serves
four audiences without diluting the research and roadmap material already in the
repo:

1. People new to automated reasoning, SAT/SMT, proof certificates, and solver
   architecture.
2. Users who want to run Axeyum on a query or corpus.
3. Contributors who need to add operators, rewrites, solver paths, or evidence.
4. Researchers/maintainers who need the full design record, roadmap, and ADRs.

The main principle is separation of concerns: the README should be the lobby,
not the entire building. Deep status, roadmap, architecture, and research notes
belong under `docs/`.

## Goals

- Make the project approachable to a technically capable reader who is new to
  SAT/SMT/proof-producing solvers.
- Preserve the honest current-state message: Axeyum is a serious research-grade
  Rust stack, not yet a general Z3 replacement or full Lean-parity prover.
- Make "what works today" easier to distinguish from "north star" and
  "experimental/incomplete."
- Give users one small query they can run quickly.
- Give contributors clear obligations for new public surface:
  semantics, replay/model support, evidence/proof route, tests, and benchmark
  artifacts.
- Keep the existing research/plan/ADR material intact and better indexed.

## Recommended README Shape

The top-level [README](../README.md) should become shorter and more
product-facing. It should answer five questions quickly:

1. What is Axeyum?
2. What can I do with it today?
3. What is still experimental or incomplete?
4. How do I run one query?
5. Where do I go next?

Suggested outline:

```md
# Axeyum

One sentence:
A Rust-first automated reasoning stack built around untrusted search and
trusted checking.

## Why It Exists

- SMT/SAT-style solving for verification, symbolic execution, and optimization.
- Pure Rust default build.
- Every `sat` should replay against the original query.
- Every `unsat` should move toward small checkable evidence.

## Current Status

- Good today: typed IR, QF_BV path, SMT-LIB front door, model replay, many
  proof/evidence routes.
- In progress: performance parity, full SMT-LIB command semantics, complete
  proof coverage.
- Not yet: general Z3 replacement, full Lean parity, complete quantifier/NRA/
  unbounded-string support.

Link to the capability matrix, support matrix, trust ledger, and latest review.

## Quick Start

Show install/build, one test command, one tiny SMT-LIB query, and the micro
benchmark command.

## First Example

Show one Rust example and one SMT-LIB example.

## Documentation

List reader paths:
- New to SAT/SMT? Start with `docs/learn/`.
- Want to use Axeyum? Read `docs/user-guide/`.
- Want to contribute? Read `docs/contributor-guide/`.
- Want internals? Read `docs/internals/`.
- Want roadmap/state? Read `PLAN.md`, `docs/PROJECT-STATE.md`, and `docs/plan/`.

## Project Layout

Short crate table.

## Development

Keep common commands only. Move long benchmark recipes into docs.

## License
```

The README should avoid leading with "100% Z3 + Lean parity." Keep that as the
north star, but phrase the public opening more cautiously:

> Axeyum's long-term target is Z3-class solving with Lean-grade checkable
> evidence. Today it is a research-grade Rust stack with strong foundations,
> broad partial coverage, and explicit `unknown`s where support or performance
> is incomplete.

## Proposed Docs Tree

Add the following structure over time:

```text
docs/
  README.md

  learn/
    README.md
    01-what-is-automated-reasoning.md
    02-sat-in-15-minutes.md
    03-smt-and-theories.md
    04-bit-vectors-and-bit-blasting.md
    05-models-unsat-and-unknown.md
    06-proofs-certificates-and-trust.md
    07-how-axeyum-solves-a-query.md
    glossary.md

  user-guide/
    README.md
    installation.md
    first-smtlib-query.md
    rust-embedding.md
    models-and-replay.md
    unsat-evidence.md
    benchmarks.md
    wasm.md
    limitations.md

  contributor-guide/
    README.md
    development-setup.md
    testing-and-validation.md
    adding-an-operator.md
    adding-a-rewrite.md
    adding-a-solver-route.md
    proof-and-evidence-obligations.md
    benchmark-artifacts.md

  reference/
    README.md
    public-api.md
    solver-config.md
    supported-logics.md
    support-matrix.md
    trust-ledger.md
    smtlib-support.md

  internals/
    README.md
    architecture.md
    term-ir.md
    evaluator.md
    rewriting.md
    bit-blasting.md
    cnf-and-sat.md
    solver-dispatch.md
    proof-stack.md
    lean-kernel.md
    documentation.md

  curriculum/
  plan/
  research/
  reviews/
```

The existing `docs/research/`, `docs/plan/`, `docs/curriculum/`, and
`docs/reviews/` directories should remain. The new directories are front doors
and guides, not replacements for the research record.

## Reader Paths

### New to Automated Reasoning

Start with:

1. `docs/learn/01-what-is-automated-reasoning.md`
2. `docs/learn/02-sat-in-15-minutes.md`
3. `docs/learn/03-smt-and-theories.md`
4. `docs/learn/05-models-unsat-and-unknown.md`
5. `docs/learn/07-how-axeyum-solves-a-query.md`

Goal: understand enough vocabulary to read the README, run a query, and know
why `sat`, `unsat`, and `unknown` are different kinds of results.

### New User

Start with:

1. `docs/user-guide/installation.md`
2. `docs/user-guide/first-smtlib-query.md`
3. `docs/user-guide/rust-embedding.md`
4. `docs/user-guide/models-and-replay.md`
5. `docs/user-guide/limitations.md`

Goal: run Axeyum, get a model, understand replay, and avoid overreading current
support.

### New Contributor

Start with:

1. [PLAN.md](../PLAN.md)
2. [Project State](PROJECT-STATE.md)
3. [`docs/contributor-guide/development-setup.md`](contributor-guide/development-setup.md)
4. [`docs/contributor-guide/testing-and-validation.md`](contributor-guide/testing-and-validation.md)
5. [`docs/contributor-guide/proof-and-evidence-obligations.md`](contributor-guide/proof-and-evidence-obligations.md)
6. [docs/plan/01-dependency-dag.md](plan/01-dependency-dag.md)

Goal: understand the session protocol and the obligations for changing public
semantics, rewrites, encodings, solver routes, and evidence.

### Maintainer/Researcher

Start with:

1. [docs/plan/00-north-star.md](plan/00-north-star.md)
2. [docs/plan/01-dependency-dag.md](plan/01-dependency-dag.md)
3. [docs/research/README.md](research/README.md)
4. [docs/research/08-planning/capability-matrix.md](research/08-planning/capability-matrix.md)
5. [docs/research/08-planning/support-matrix.md](research/08-planning/support-matrix.md)
6. [docs/research/08-planning/trust-ledger.md](research/08-planning/trust-ledger.md)
7. [docs/research/09-decisions/README.md](research/09-decisions/README.md)

Goal: understand the design, status, tradeoffs, and accepted decisions.

## Beginner Material Strategy

The beginner docs should not begin with Axeyum internals. They should introduce
concepts through tiny examples:

```text
A solver answers questions like:
  "Is there an input that makes this condition true?"

SAT:
  Boolean variables only.

SMT:
  Boolean structure plus theories:
  bit-vectors, integers, arrays, functions, floating point, strings.

sat:
  A model exists. Axeyum checks it by evaluating the original query.

unsat:
  No model exists. Axeyum tries to provide a small certificate/checker route.

unknown:
  The solver did not prove either side. This is a valid result, not a crash.
```

The first complete walkthrough should use one small bit-vector query:

```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x #x01) #x00))
(check-sat)
(get-model)
```

Explain:

- `x` ranges over 256 8-bit values.
- `#xff + #x01` wraps to `#x00`.
- A satisfying model is `x = #xff`.
- Axeyum can replay the model against the original assertion.
- Internally, bit-vector operators can be lowered to Boolean circuits and SAT.

Then show the contradictory version:

```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x00))
(assert (= x #x01))
(check-sat)
```

Explain `unsat` and the proof/certificate idea without diving into DRAT/Alethe
yet.

## Content Boundaries

Use these rules to keep the docs maintainable:

- README: public promise, quick start, status summary, navigation.
- `docs/learn/`: concepts, no implementation detail beyond simple diagrams.
- `docs/user-guide/`: how to run and interpret Axeyum.
- `docs/contributor-guide/`: how to safely change Axeyum.
- `docs/reference/`: generated or stable API/support facts.
- `docs/internals/`: implementation architecture.
- `docs/research/`: design notes and research context.
- `docs/plan/`: roadmap and active engineering plan.
- `docs/reviews/`: audits and external reviews.

## Initial Implementation Sequence (completed)

The first bounded documentation slice was deliberately small and mostly
additive:

1. Rewrite [README.md](../README.md) into the shorter landing page shape.
2. Add `docs/README.md` as the documentation hub.
3. Add `docs/learn/README.md`.
4. Add `docs/learn/01-what-is-automated-reasoning.md`.
5. Add `docs/user-guide/first-smtlib-query.md`.
6. Add `docs/user-guide/limitations.md`.
7. Add `docs/user-guide/benchmarks.md` and move the long benchmark command list
   out of the README.

It avoided reorganizing `docs/research/` and `docs/plan/`, linked to them, and
left migration of duplicated content to later evidence-driven increments. This
list is retained as design rationale, not as the current action queue.

## Current Maintenance Sequence

Current sequence:

1. Beginner, user-guide, contributor, reference, internals, crate, curriculum,
   review, plan, and research front doors are complete and indexed.
2. Deep-page audits corrected the curriculum depth/backlog, documentation-build
   instructions, reconstruction-target wording, textbook/NRA maps, public
   arithmetic state, example discoverability, and historical-parity routing.
   Continue incrementally when a live guide exposes a concrete stale claim;
   preserve dated reviews, preregistrations, results, and research notes as
   snapshots.
3. Keep generated capability/support/trust authorities and relative-link CI
   green as documentation changes.
4. Treat a full mdBook-render CI gate as separate future work; the current
   hosted documentation workflow does not run it.

## Documentation Quality Bar

- Every claim about support should link to the support matrix, capability
  matrix, trust ledger, or a benchmark artifact.
- Every example should be runnable.
- Every definitive solver result in examples should explain model replay or
  proof/evidence at the appropriate level.
- `unknown` should be described positively: honest incompleteness/resource
  control, not failure.
- Beginner pages should define terms before using abbreviations like QF_BV,
  EUF, CNF, DRAT, Alethe, or MBQI.
- Roadmap claims should use concrete fragment milestones, not broad parity
  language.

## Current Pointers

- Current live tracker and master plan: [PLAN.md](../PLAN.md)
- Full engineering plan: [docs/plan/README.md](plan/README.md)
- Research index: [docs/research/README.md](research/README.md)
- Capability matrix: [docs/research/08-planning/capability-matrix.md](research/08-planning/capability-matrix.md)
- Support matrix: [docs/research/08-planning/support-matrix.md](research/08-planning/support-matrix.md)
- Trust ledger: [docs/research/08-planning/trust-ledger.md](research/08-planning/trust-ledger.md)
- Codex review: [docs/reviews/codex-20260620/report.md](reviews/codex-20260620/report.md)
