# Benchmarking And Performance Methodology

Status: draft
Last updated: 2026-06-12

## Purpose

Define how performance claims are measured and how performance-driven
decisions are gated. Several roadmap decisions ("custom SAT only when
benchmarks justify it") currently reference benchmarks that have no defined
methodology; this note makes those gates concrete and falsifiable.

## Scope

In scope:

- Corpus tiers, metrics, scoring, harness requirements, and decision gates.

Out of scope:

- Specific performance targets and final benchmark numbers.

## Core Claims

- No optimization or engine-replacement decision is made without a named
  corpus and a recorded baseline run.
- Three corpus tiers serve different questions:
  microbenchmarks answer "did this code change regress",
  public competition sets answer "where are we relative to the field",
  client-generated queries answer "does this matter for real workloads".
- Wall time alone is insufficient; layer-attributed time (rewrite, lower,
  encode, SAT) is what justifies replacing a layer.
- PAR-2 scoring with fixed timeout (the SAT/SMT competition convention) is the
  cross-corpus comparison metric, so results are comparable to published data.

## Corpus Tiers

| Tier | Contents | Question answered |
|---|---|---|
| Micro | Hand-written op-level cases, exhaustive small widths. | Regression per code change. |
| Public | SMT-LIB QF_BV / QF_ABV sets, SAT Competition CNF, HWMCC BTOR2. | Standing vs. mature solvers. |
| Client | Minimized queries captured from real frontends. | Real-workload relevance. |

## Metrics

- Wall time, PAR-2 over corpus, timeout count.
- Layer attribution: time in rewriting, bit-blasting, CNF encoding, SAT, model
  lifting.
- Encoding size: term nodes in/out of rewriter, AIG nodes, CNF vars/clauses.
- SAT internals: propagations, conflicts, decisions, learned/deleted clauses.
- Peak memory per phase.

## Decision Gates

- Custom CDCL core: building it is settled identity, not contingent
  ([ADR-0002](../09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md));
  this gate decides *priority*. It jumps the queue ahead of encoding work
  when, on the public + client tiers, (a) SAT time dominates end-to-end
  time, and (b) the best Rust adapter shows a consistent material gap to
  CaDiCaL/Kissat on Axeyum-generated CNF specifically. Until then, effort
  goes to encodings first.
- Word-level/lazy techniques (beyond-bit-blasting note): justified per
  technique by layer attribution showing the targeted operator class dominates.
- Backend default choice: highest PAR-2 on the client tier wins, revisited per
  release.

## Design Implications

- Build the harness early (`axeyum-bench` binary): runs a corpus against a
  named config, emits a versioned results artifact (source label, logic,
  selected families, config hash, corpus hash, solver versions, hardware note,
  seed). Artifact version 4 records the selected backend kind, timeout/limit
  config, deterministic corpus/config hashes, machine note, rewrite mode and
  enabled rule IDs, PAR-2 summary, per-instance input/output shape metrics,
  rewrite rule counts, original-vs-rewritten backend decision comparison,
  backend layer statistics such as AIG nodes and CNF variables/clauses for the
  pure Rust path, layer timings, unsupported/error triage, and `sat`
  model-replay failures against the original assertions. Artifact version 5
  extends that schema with node-budget provenance and optional Z3 oracle
  comparison fields, so pure-Rust public baselines can distinguish admitted
  decisions, budget-driven `unknown`, unsupported features, and soundness
  disagreements. Artifact version 6 extends the admission and planning
  provenance with CNF variable/clause budgets and the submitted query-plan mode
  plus `sat` replay-failure policy, so a wider node gate can be bounded before
  SAT solve and sliced/planned runs can be interpreted without weakening the
  original-query replay contract. Artifact version 7 adds replay-refinement
  limits and per-instance refinement telemetry, so query-planning experiments
  can report how many replay failures were used to grow a support slice and why
  refinement stopped. Artifact version 8 adds the harness `jobs` setting to
  distinguish single-instance solver timings from corpus-level parallel
  throughput when long public diagnostics are run with Rayon workers.
  Artifact version 9 adds replay-refinement batch size to the query-plan
  configuration, so exact-target refinement runs can distinguish "one failed
  original assertion per round" from batched failed-assertion admission while
  preserving full-query replay before any `sat` is accepted.
  Artifact version 10 adds the adaptive-batch flag and per-instance backoff
  count, so budget-aware refinement runs can be separated from static batch
  runs in both the JSON config and config hash.
  Artifact version 11 adds replay-refinement selection policy, so source-order
  failed-assertion refinement can be compared with deterministic cost-shaped
  selection heuristics without weakening the replay contract. Artifact version
  12 records the bounded plan-aware selection option and current root-direct
  assertion CNF encoder behavior, so plan-local and plan-aware refinement
  diagnostics can be separated in artifacts.
- Fixed seeds and pinned solver versions everywhere; repeated runs with
  variance reported for anything under a few seconds.
- Corpus-level parallelism is an execution accelerator, not a solver-quality
  claim by itself: artifacts must preserve deterministic file ordering and
  per-instance model replay/oracle comparison, and single-instance solver
  timings remain the evidence for encoding or SAT-core priority decisions.
- Statistics counters from sat-core-state and performance notes feed this
  harness; they are requirements, not nice-to-haves.
- CI runs the micro tier per PR through `axeyum-bench`; public-tier runs are
  scheduled, not per-PR.

## Risks

- Public corpora overweight problem classes Axeyum does not target; the
  client tier must exist before big architectural bets.
- Benchmark harnesses rot without scheduled runs and stored baselines.

## Open Questions

- [ ] What hardware baseline is recorded as canonical for published numbers?
- [ ] How large can the per-PR micro tier be before CI cost bites?
- [ ] Should published long-run results artifacts live in-repo, in CI storage,
      or a separate repo?
  - Current convention: small baseline artifacts live in
    `bench-results/baselines/`; local scratch runs stay in gitignored
    `bench-results/local/`.

## Source Pointers

- SMT-COMP rules and scoring: https://smt-comp.github.io/
- SAT Competition: https://satcompetition.github.io/
- SMT-LIB benchmarks: https://smt-lib.org/benchmarks.shtml
- Hardware model checking competition: https://hwmcc.github.io/
