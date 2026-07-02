# Solver Reuse Queries

This is the consumer-facing query guide for resource packs that have crossed
the R5 solver-feedback boundary. It complements the general
[Foundational Resource Consumer Queries](CONSUMER-QUERIES.md), the
[Proof Route Query Matrix](PROOF-ROUTE-QUERY-MATRIX.md), and the
[Proof Upgrade Frontier](PROOF-UPGRADE-FRONTIER.md).

Use this guide when a solver, proof, benchmark, or fuzzing contributor wants to
mine the current math resources by solver pressure without reading every pack.

## Boundary

`solver_reuse=promoted` means the pack is reusable by solver work because its
mathematical meaning, validation command, and trust boundary are explicit. It
does not mean:

- the row is a general theorem;
- the row is a Z3/cvc5 parity claim;
- every row in the pack has a checked proof object;
- the pack belongs in a performance benchmark without route-specific review.

The source pack stays educational. Solver reuse is a back-link from that source
object into regressions, fuzz seeds, benchmark slices, or explicit
non-benchmark-horizon decisions.

## Start Here

List all promoted packs:

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse promoted \
  --require-any
```

Get the public contract counts first when validating a checkout:

```sh
python3 scripts/query-foundational-resources.py summary
```

Today the summary reports every current non-template math pack as promoted for
solver reuse. New packs should not be promoted by default; they should move
through candidate, promoted, non-benchmark-horizon, or unclassified status
deliberately.

## Route-Scoped Promoted Packs

Farkas / QF_LRA rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse promoted \
  --route Farkas \
  --require-any
```

Alethe / QF_UF rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse promoted \
  --route Alethe \
  --require-any
```

Diophantine / QF_LIA rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse promoted \
  --route Diophantine \
  --require-any
```

QF_BV / bit-blast proof rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse promoted \
  --route qf-bv \
  --require-any
```

These pack-level route queries return route-specific check labels and
validation labels when a concrete row matches. `pack-metadata` means the pack
advertises the route even when no individual check label contains the route
substring.

## Field-Scoped Solver Mining

Graph resources:

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse promoted \
  --field graph_theory \
  --require-any
```

Optimization/Farkas resources:

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse promoted \
  --field optimization_and_convexity \
  --route Farkas \
  --require-any
```

Algebra/Alethe resources:

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse promoted \
  --field abstract_algebra \
  --route Alethe \
  --require-any
```

Use field filters to choose a corpus theme. Use route filters to choose the
solver or proof machinery that the theme pressures.

## Checked Row Drilldowns

Promoted packs are the R5 unit. Concrete checked rows still come from the
`checks` view:

```sh
python3 scripts/query-foundational-resources.py checks \
  --route Farkas \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

```sh
python3 scripts/query-foundational-resources.py checks \
  --route Alethe \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

```sh
python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

These row-level queries are the right starting point for a regression or fuzz
seed. Before promoting one into a solver suite, keep the resource pack path in
the test or corpus metadata so the educational source and trust story remain
traceable.

## Review Before Benchmarking

Use solver-reuse metadata to find candidates. Before adding a row to a
performance benchmark:

- confirm the row is not `lean-horizon`;
- confirm the expected result has deterministic replay or checked evidence;
- confirm the encoding is representative of the solver feature under test;
- keep bounded finite examples separate from general theorem claims;
- record whether the row is a regression, fuzz seed, benchmark slice, or
  explicit non-benchmark horizon.

This keeps the resource layer useful to solver work without turning educational
examples into inflated parity claims.
