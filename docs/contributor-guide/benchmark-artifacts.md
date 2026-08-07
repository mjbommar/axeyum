# Benchmark Artifacts

Benchmarks in Axeyum are evidence, not decoration. A useful artifact fixes the
code, inputs, configuration, resources, oracle, and replay policy tightly enough
that another contributor can reproduce the cell and explain any difference.

## Start with a question

Write the claim before running the benchmark. Examples:

- Does one rewrite reduce DAG/CNF size without changing verdicts?
- Does a route expand the decided set at the same resource policy?
- Is a regression in parsing, rewriting, lowering, SAT search, model lift, or
  proof checking?
- Does a result survive repeated runs and an independent oracle comparison?

Do not collect a large matrix before deciding which comparison will answer the
question.

Read the [benchmarking methodology](../research/08-planning/benchmarking-and-performance-methodology.md)
and the current [benchmark artifact index](../../bench-results/README.md).

## Scratch before committed evidence

Use the committed micro corpus for a fast harness check:

```sh
just bench-micro
```

For ad hoc repository-local output, write under `bench-results/local/`, which is
gitignored. Do not overwrite a committed baseline while experimenting.

The pure-Rust and Z3 micro recipes are:

```sh
just bench-micro
just bench-micro-z3
```

The Z3 run is a differential/oracle cell and requires its native feature
profile. It is not the default product dependency.

## Bind code and inputs immutably

Every retained artifact must identify:

- full Git commit ID, not only a branch name;
- whether the source tree was required to be clean;
- corpus manifest or an exact sorted file list;
- content hashes for external or mutable inputs;
- selection tier/filter and expected verdict source; and
- harness/schema version.

For a historical replay, read inputs from the recorded Git object (`git show
<sha>:<path>`) rather than a moving `origin/main`. A current branch name is not
historical evidence.

External client corpora need a committed manifest even when the query bytes
cannot be redistributed. The manifest should bind membership, hashes, families,
tiers, and trusted expected verdicts.

## Fix the experiment policy

Record all variables that can change work or outcomes:

- backend and exact version;
- feature profile and native library identity;
- rewrite/query-plan/solver configuration;
- timeout, deterministic resource, node, CNF, memory, and proof budgets;
- jobs/threads and worker pinning;
- random seed;
- warm versus cold lifecycle;
- preprocessing/inprocessing flags;
- model replay and proof-checking policy; and
- relevant hardware and operating-system identity.

Budgets with the same number are not necessarily equivalent across backends.
Name the unit and backend. Wall time is useful for user-visible performance;
deterministic resource limits are preferable for regression attribution.

## Design controlled comparisons

For an A/B claim, change one lever:

| Fixed | Changed |
|---|---|
| commit or explicitly paired commits | the intended implementation |
| corpus membership and input bytes | one route/rewrite/configuration lever |
| timeout and deterministic budgets | nothing else |
| jobs, lifecycle, host, tool versions | |
| oracle and replay policy | |

Run a retained baseline/control in the same environment as the treatment. If
the control also moves, investigate environment or workload drift before
crediting the change.

Use repetitions when timing is part of the claim. Report the individual runs or
distribution, not only the best sample. Never present a single noisy timing as a
stable speedup.

## Soundness gates precede speed claims

A benchmark cell is invalid for performance credit if it contains:

- a wrong definitive verdict;
- a source-model replay failure;
- a missing required proof check;
- an operational error counted as `unknown` or timeout;
- an input outside the declared manifest/tier; or
- a different oracle/resource policy between control and treatment.

Report `sat`, `unsat`, each structured `unknown` class, unsupported, parse/
solver errors, replay failures, proof-check states, oracle agreements, and
disagreements separately. “Decided” must not absorb errors.

If any row says expected `unsat` but got `sat`, stop performance analysis and
root-cause the soundness failure first.

## Attribute the pipeline

Retain shape and time fields that localize movement:

- input and rewritten DAG nodes;
- rule applications;
- AIG nodes and CNF variables/clauses;
- parse, rewrite/plan, lowering, CNF, SAT/theory solve, model-lift/replay, and
  proof-check times; and
- backend-specific counters with their versioned meaning.

An end-to-end improvement without layer data is still useful, but it cannot
justify a claim about which subsystem caused it.

## Commit only a reproducible result

A committed artifact should include or link:

1. the machine-readable raw result;
2. the exact reproduction command or named `just` recipe;
3. the input/corpus manifest;
4. a short Markdown interpretation with limits;
5. a regenerator for derived tables/plots; and
6. validation that generated summaries match raw data.

Use stable ordering and avoid timestamps in content-addressed comparisons unless
they are normalized out. Generated dashboards should fail `--check` when stale.

Update [`bench-results/README.md`](../../bench-results/README.md), the relevant
roadmap/ADR, and `PLAN.md` only after the artifact exists. Keep current measured
facts separate from future targets.

## Review checklist

- [ ] The benchmark answers a written question with a named control.
- [ ] Full source revision and clean/dirty policy are recorded.
- [ ] Corpus membership and bytes are immutable or hash-bound.
- [ ] Backend, tools, features, budgets, seeds, jobs, lifecycle, and host are recorded.
- [ ] Wrong verdicts, errors, replay failures, and proof gaps are zero or surfaced first.
- [ ] A/B cells change only the intended lever.
- [ ] Repetitions support timing claims.
- [ ] Layer shape/time data supports attribution.
- [ ] Raw JSON, command, manifest, interpretation, and regenerators agree.
- [ ] Scratch output was not mistaken for a committed baseline.

