# Finite Model Replay Evidence

## Problem Shape

Tiny witnessed shape:

```text
1/3 < m < 2/3
m = (1/3 + 2/3) / 2
```

Expected result: `sat`, with `m = 1/2`.

This is the route used by most small math resource packs: exact finite data,
fixed rational witnesses, finite tables, or bounded traces are accepted only
after replaying the claimed result against the original mathematical model.

## Solver Route

For satisfiable examples, the search route may be a solver, a hand-written
example pack witness, or a small deterministic enumeration. The result is not
trusted merely because it was found. It is accepted only after the original
claim is re-evaluated on the returned witness.

For finite `unsat` examples that are still marked `replay-only`, the checker
must enumerate the fixed finite search space or recompute the fixed
contradiction directly. This is not a general proof route; it is a bounded
finite replay route.

## Evidence Artifact

Current checked artifacts are small and inspectable:

- `expected.json` witnesses and check rows;
- exact rational, integer, set, graph, table, or trace data;
- a deterministic validation function in
  [scripts/validate-foundational-example-pack.py](../../../scripts/validate-foundational-example-pack.py).

There is no separate proof object for this route. The artifact is the witness
plus the independent replay checker.

## Checker

The foundational example-pack validator replays each supported pack-specific
model. Examples include exact rational arithmetic, graph colorings, finite
cardinality witnesses, bounded induction obligations, finite topology
closure/interior, finite measure additivity, recurrence traces, finite operator
norms, and exact table statistics.

The checker rejects malformed data, non-deterministic references, missing
witnesses, failed arithmetic equalities, violated finite axioms, and claimed
finite `unsat` rows that still have a counterexample.

## Lean Reconstruction

Status: intentionally out of scope for this route.

Replay proves the fixed finite artifact, not the general theorem behind the
lesson. If a resource needs a kernel proof of a general theorem, it must link a
specific Lean recipe or remain under the
[Lean Horizon Template](lean-horizon-template.md).

## Trust Boundary

Trusted:

- not the search that found the model;
- not any broad theorem suggested by the example prose.

Checked:

- the witness against the original finite claim;
- exact arithmetic and finite enumeration in the validator;
- source-reference and metadata consistency.

Downgrade behavior:

- if replay fails, the example is invalid;
- if the finite checker does not cover the claim shape, keep the proof route as
  `proof-gap` or `lean-horizon`.

## Commands

All math packs:

```sh
python3 scripts/validate-foundational-example-pack.py
```

Focused examples:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cardinality-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-obligations-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
```

## Links

- [SMT Fragment Atlas](../../atlas/README.md)
- [support matrix](../../research/08-planning/support-matrix.md)
- [trust ledger](../../research/08-planning/trust-ledger.md)
- [Math Curriculum Resource Buildout](../../foundational-resources/MATH-CURRICULUM-BUILDOUT.md)
- [example-pack schema](../../../artifacts/ontology/foundational-example-pack.schema.json)
- [Finite Cardinality pack](../../../artifacts/examples/math/finite-cardinality-v0/)
- [Induction Obligations pack](../../../artifacts/examples/math/induction-obligations-v0/)
