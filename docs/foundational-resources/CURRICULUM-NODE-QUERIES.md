# Curriculum Node Queries

This is the consumer-facing query guide for starting from the formal
curriculum DAG and drilling into resource packs, concepts, proof routes, and
theorem boundaries. It complements the general
[Foundational Resource Consumer Queries](CONSUMER-QUERIES.md), the
[Field Readiness Query Matrix](FIELD-READINESS-QUERY-MATRIX.md), and the
[University Math Field Taxonomy](MATH-FIELDS.md).

Use this guide when a learner, educator, or resource consumer starts with a
curriculum node such as `sets`, `linear-algebra`, `modular-arithmetic`, or
`calculus` rather than with a field or proof route.

## Boundary

The curriculum-node view is an entry point, not a theorem claim. A node can
have:

- checked finite or computable examples;
- replay-only rows that are already the right trusted small checker;
- route-specific proof rows;
- Lean-horizon rows for general theorem statements.

Do not infer that a curriculum node is fully taught or fully proved because it
has validated packs. Read the row-level proof status and theorem horizon before
making coverage claims.

## Start Here

List the curriculum-node atlas rows:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --kind curriculum-node \
  --require-any
```

Inspect one node:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --curriculum-node sets \
  --require-any
```

Find packs attached to that node:

```sh
python3 scripts/query-foundational-resources.py packs \
  --curriculum-node sets \
  --require-any
```

`concepts` and `packs` support direct `--curriculum-node` filtering. The
`checks` view intentionally stays row-centered and filters by pack, field,
concept, route, proof status, result, validation label, or text.

## Foundations Example

Start from `sets`:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --curriculum-node sets \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --curriculum-node sets \
  --require-any
```

Then drill into checked set/foundation rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field set_theory_and_foundations \
  --proof-status checked \
  --require-any
```

And theorem boundaries:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field set_theory_and_foundations \
  --proof-status lean-horizon \
  --require-any
```

This separates finite set, relation, quotient, and cardinality checks from
general cardinality, compactness, and algebraic theorem horizons.

## Linear Algebra Example

Start from the curriculum node:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --curriculum-node linear-algebra \
  --require-any
```

Find exact-rational proof-route packs:

```sh
python3 scripts/query-foundational-resources.py packs \
  --curriculum-node linear-algebra \
  --route Farkas \
  --require-any
```

Drill into checked rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field linear_algebra \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Use this path for LU, nullspace, residual, least-squares, optimization, and
finite matrix-computation rows. It keeps finite matrix replay distinct from
benchmark and theorem claims.

## Number And Algebra Example

Compare fixed-width and integer routes for modular arithmetic:

```sh
python3 scripts/query-foundational-resources.py packs \
  --curriculum-node modular-arithmetic \
  --route qf-bv \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --curriculum-node modular-arithmetic \
  --route Diophantine \
  --require-any
```

Then drill into checked arithmetic evidence:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field number_theory \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field number_theory \
  --route qf-bv \
  --proof-status checked \
  --require-any
```

This shows the difference between fixed-width residue obligations and integer
linear obstruction rows.

## Calculus And Analysis Example

Start from bounded calculus resources:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --curriculum-node calculus \
  --require-any
```

Find packs that explicitly expose theorem horizons:

```sh
python3 scripts/query-foundational-resources.py packs \
  --curriculum-node calculus \
  --route lean-horizon-template \
  --proof-status lean-horizon \
  --require-any
```

This path is useful for calculus shadows, finite optimization steps, line
searches, and numerical methods. The finite rows are executable resources; the
general differentiability, convergence, KKT, and optimization theorems remain
Lean-horizon work until kernel-checked reconstruction exists.

## Reading Order

For a curriculum node:

1. Query the `curriculum-node` concept row.
2. Query the attached packs.
3. Drill into checked rows by field, route, concept, or pack.
4. Check `lean-horizon` rows before describing theorem coverage.
5. Use [Proof Upgrade Queries](PROOF-UPGRADE-QUERIES.md) before promoting a
   replay-only row.
6. Use [Solver Reuse Queries](SOLVER-REUSE-QUERIES.md) before mining a row for
   regressions, fuzzing, or benchmarks.

This preserves the resource invariant:

```text
curriculum node -> concept row -> example pack -> learner path -> proof route
-> solver reuse -> consumer boundary
```
