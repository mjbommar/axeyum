# Adding a Rewrite

A rewrite changes the formula that a solver sees. Treat it as a semantic proof
obligation with telemetry, not as a convenient pattern replacement.

## 1. Classify the transformation

Axeyum distinguishes:

- **denotation-preserving:** the rewritten term has exactly the same value in
  every model; and
- **equisatisfiable:** satisfiability is preserved, but source variables or
  values may need reconstruction.

Read the rewrite entry gate in the
[foundational DAG](../research/08-planning/foundational-dag.md#phase-3-entry-rewriting-and-query-planning)
and [ADR-0005](../research/09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md).
Default rewrites remain denotation-preserving unless an explicit model
projection and replay route is implemented and tested.

Before implementation, write the exact precondition, preservation class,
termination argument, model-projection effect, test route, and expected measured
benefit. If any of those is unknown, the rule is not ready for default use.

## 2. Register the manifest contract

Every rule has metadata defined in
[`axeyum-rewrite`](../../crates/axeyum-rewrite/src/lib.rs):

- a stable lowercase [`RewriteRuleId`](../../crates/axeyum-rewrite/src/lib.rs);
- a human-readable name;
- an exact sort/width/operator precondition;
- `Preservation::Denotation` or `Preservation::Equisatisfiable`;
- `ModelProjection::Identity`, `Required`, or `Implemented`;
- one or more `RewriteTestRoute` values; and
- explicit default enablement.

The manifest rejects duplicate IDs, missing preconditions/tests, and unsafe
default combinations. Do not bypass it with an unregistered local fold.

Version the rule ID when its semantics or precondition changes. Artifact and
ablation histories rely on stable IDs.

## 3. Implement deterministic matching

The default canonicalizer lives in
[`canonical.rs`](../../crates/axeyum-rewrite/src/canonical.rs). Preserve:

- bottom-up rebuilding and arena interning;
- stable operand ordering for commutative normalization;
- bounded local fuel and a termination measure;
- deterministic rule priority and reporting; and
- source-to-output information needed by model reconstruction.

Never use hash-map iteration order to select a result. A rule that can grow or
cycle needs a well-founded measure and a hard deterministic bound that safely
declines or stops.

## 4. Test semantics, not just shape

A pattern test such as “`x + 0` becomes `x`” is necessary but insufficient.
Add the routes named by the manifest:

1. exact positive cases and near-miss cases where the rule must not fire;
2. exhaustive small-width evaluator equivalence where finite;
3. deterministic generated evaluator equivalence for broader terms;
4. oracle differential checks on complete queries;
5. rule-order and fuel/termination tests; and
6. model-projection replay for every equisatisfiable rule.

For denotation preservation, evaluate both source and result under the same
assignment. For equisatisfiability, test both verdict directions and reconstruct
a source model from a transformed satisfying model.

Retain a non-trigger control. A rule that never fires can otherwise make an
equivalence suite look green.

## 5. Preserve replay and evidence

The solver must still check `sat` against the original, pre-rewrite assertions.
Identity projection is valid only when symbols and their meanings are preserved.
Variable elimination, abstraction, or fresh symbols require a reconstruction
trail.

For `unsat`, state how rewrite correctness composes with the downstream proof:

- exact denotation may use a checked equivalence argument;
- equisatisfiable preprocessing needs a checked transformation certificate or
  a clearly ledgered meta-argument; and
- a proof over only the rewritten query must not be presented as an
  independently checked proof of the source query unless the bridge is checked.

Use [Proof and evidence obligations](proof-and-evidence-obligations.md) to
classify the resulting assurance honestly.

## 6. Measure the rule

A correct default rewrite must also earn its cost. Use an A/B comparison over
the same immutable corpus, commit, budgets, jobs, oracle, and repetitions:

```text
control:   rewrite disabled (or the prior manifest)
treatment: prior manifest plus exactly this rule
```

Record at least rule applications, input/output DAG nodes, lowering/CNF shape,
decision changes, replay failures, and layer timings. Never credit a win that
also changes the query set, resource policy, or oracle.

Scratch artifacts belong under `bench-results/local/`; see
[Benchmark artifacts](benchmark-artifacts.md) before committing a baseline.

## 7. Update the decision and support record

Update the manifest, relevant ADR/roadmap entry, benchmark evidence, and
`PLAN.md`. If default behavior changes, say so in user-facing limitations or
release notes. Do not describe an off-by-default experiment as active solver
behavior.

## 8. Validate

```sh
cargo test -p axeyum-rewrite
cargo clippy -p axeyum-rewrite --all-targets -- -D warnings
cargo test -p axeyum-solver --features full
just check-scope origin/main
```

Run the focused corpus A/B before the full gate. Then run `just check` once at
the integration boundary.

## Completion checklist

- [ ] Stable rule ID, precondition, preservation, projection, and test routes exist.
- [ ] Matching, priority, fuel, and output are deterministic.
- [ ] Positive, near-miss, exhaustive/property, and differential tests pass.
- [ ] Source-query SAT replay and any reconstruction trail are tested.
- [ ] UNSAT proof composition or trust limitation is explicit.
- [ ] A controlled A/B artifact demonstrates cost and benefit.
- [ ] Default enablement matches the manifest, docs, ADR, and benchmark claim.
