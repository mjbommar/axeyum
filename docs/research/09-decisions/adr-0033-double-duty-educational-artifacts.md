# ADR-0033: Double-duty educational artifacts (test/benchmark = curriculum)

Status: accepted
Date: 2026-06-17

## Context

Axeyum needs a richer suite of testing and benchmarking artifacts (the
[foundational example-suites note](../08-planning/foundational-example-suites.md)
scopes the tiers A/B/C/D). Separately, those artifacts are wanted as
*educational content* about mathematics, proof systems, and software
verification. This ADR closes the question of **whether education is a separate
build or the same artifacts** and fixes the contract and crate boundary so the
two goals do not fork.

The note's thesis: the architecture that makes an artifact a good test is the
same one that makes it good educational content. A self-checking scenario that
is seeded/parametric, known-by-construction, evidence-exhibiting, and placed in
a concept DAG is simultaneously a regression test, a benchmark instance, and a
homework problem with a sound auto-grader and a worked solution. Axeyum already
has the four hard-to-get assets: sound grading via *trusted checking*
(`eval`/`check_alethe`), certified procedural generation (ADR-0008's
SAT-by-execution / UNSAT-by-identity), measured difficulty (CDCL conflicts, CNF
size, proof length), and an existing concept DAG (the
[foundational DAG](../08-planning/foundational-dag.md)).

This builds on [ADR-0008](adr-0008-consumer-scenario-models.md) (self-checking
consumer scenarios) and [ADR-0001](adr-0001-vertical-slice-first.md) (add crates
only after a boundary is proven by use).

## Decision

**Educational artifacts are a second projection of the self-checking test/
benchmark artifacts, not a separate product — and they are built bottom-up,
additively, inside `axeyum-scenarios` until a boundary is proven, governed by a
double-duty contract.**

Specifically:

1. **Double-duty artifact contract.** A first-class educational/test artifact
   carries, beyond ADR-0008's `(name, family, width, seed, arena, query,
   expectation)`:
   - one or more **concept-DAG nodes** (its place in the curriculum and the
     coverage map);
   - a **problem-statement renderer** and a **solution/evidence renderer**
     (human-readable);
   - a **difficulty signal** that is *measured* (e.g. enumerated case count,
     CNF size, or proof length), not asserted.
2. **Grading is trusted checking, never search.** Any auto-grader routes a
   candidate answer through the evaluator / `evidence.check` / `check_alethe`.
   "The search returned `sat`" is never a grading oracle. A grader defect then
   yields a *failed check*, never a wrongly-accepted answer. This is ADR-0008
   restated for grading.
3. **Tier split (from the note), ratified.** Build suites A (software
   verification), B (decidable geometry / RCF), and C (finite/modular math) as
   double-duty artifacts. Tier D (induction-bearing arithmetic, ε–δ analysis) is
   **undecidable → a Lean-horizon proof-reconstruction target, never a benchmark
   instance**; it appears in the curriculum only as the "limits of automation"
   lesson.
4. **Crate boundary.** Educational capabilities (concept DAG, rendering,
   exercise/grading) start as additive modules of `axeyum-scenarios`. A separate
   `axeyum-edu` crate is deferred until the boundary is exercised (ADR-0001).
   These modules add **no new solver surface and no foundational-DAG change**.
5. **Education is a consumer/lens, not a phase.** It may not starve a foundation
   phase (the roadmap's horizon-gravity rule). Educational capability ships only
   as a byproduct of an artifact already justified as a test/benchmark.

## Evidence

- The existing `axeyum-scenarios` self-check (`Scenario::self_check`) already
  *is* a sound grader for the catalog: it evaluates a candidate witness and
  requires `true`, or enumerates the finite domain for UNSAT — both via the
  evaluator, not a solver.
- The proof track already provides `check_alethe` (internally) and Carcara
  (externally) as independent step-checkers, so a "fill the proof step" exercise
  is gradable today against real checkers, not heuristics.
- Procedural generation with certified keys is already in the crate: the seeded
  `mixing`/`machine` (SAT by execution) and `identity` (UNSAT by bounded
  enumeration) families generate parametric instances with known answers.
- The concept DAG exists as prose (`foundational-dag.md`); formalizing it is a
  representation change, not new semantics.

## Alternatives

- **A separate education product/crate up front.** Rejected: violates ADR-0001
  (boundary not yet exercised) and risks two diverging artifact sets; the whole
  value is that test and lesson are one artifact.
- **Grading via the solver result or a native oracle.** Rejected: unsound (a
  search bug would accept wrong answers) and trust-expanding (ADR-0002); the
  trusted-checker route is both sound and the project's identity.
- **Treating Peano/analysis as a benchmark tier.** Rejected: undecidable, would
  fill the numbers with `unknown`; kept as a reconstruction target only.
- **LLM-authored/graded content.** Out of scope for the certified layer; the
  narrative layer may be human/LLM-authored but the *exercises* are
  machine-certified by axeyum.

## Consequences

- **Easier:** every new self-checking scenario can become a graded exercise and
  a curriculum node at low marginal cost; the concept DAG doubles as a
  test-coverage audit (capability cells with no exercise become visible).
- **Harder / watch:** artifacts now carry rendering + concept metadata, so the
  scenario type grows; mitigated by keeping renderers and the DAG in separate,
  optional modules. Difficulty signals must be genuinely measured.
- **Revisit when:** the `axeyum-scenarios` modules outgrow the crate (extract
  `axeyum-edu` under a follow-up ADR), or when P3.6/P3.7 land (tier-D
  reconstruction targets become buildable).
- Closes the educational-lens open questions in the example-suites note;
  proposes no foundational-DAG change.

## Source Pointers

- Example-suites note: ../08-planning/foundational-example-suites.md
- ADR-0008 (consumer scenario models): adr-0008-consumer-scenario-models.md
- ADR-0001 (vertical slice, crate boundaries): adr-0001-vertical-slice-first.md
- Foundational DAG: ../08-planning/foundational-dag.md
