# Fragment Demand Queries

This is the consumer-facing query guide for asking which foundational math
resources exercise each solver fragment. It connects the math curriculum
resource corpus to the [SMT Fragment Atlas](../atlas/README.md) without
introducing a typed API or a separate repository.

Use this guide when a solver, proof, benchmark, or curriculum contributor wants
to answer:

```text
Which educational resources currently put pressure on Bool, QF_BV, QF_LIA,
QF_LRA, QF_UF, finite replay, or Lean-horizon reconstruction?
```

For route-level proof coverage, see
[Proof Route Query Matrix](PROOF-ROUTE-QUERY-MATRIX.md). For promoted
solver-reuse packs, see [Solver Reuse Queries](SOLVER-REUSE-QUERIES.md). For
proof-status boundaries, see [Trust Boundary Queries](TRUST-BOUNDARY-QUERIES.md).

## Boundary

Fragment queries are demand discovery, not parity evidence.

- A pack returned by `--fragment QF_LRA` is a source of exact-rational pressure;
  it is not a claim that Axeyum is performance-competitive with Z3/cvc5 on
  QF_LRA.
- A checked row returned by `--fragment QF_UF` is evidence for that finite row's
  equality/congruence shape; it is not a full first-order theorem.
- A replay-only row returned by `--fragment finite` can still be the correct
  trusted story.
- A Lean-horizon row returned by `--fragment Lean` is a future reconstruction
  target, not a solver result.

The public `--fragment` filter is a substring search over committed pack and
row fragment metadata. If the SMT Fragment Atlas names a frontier fragment that
does not appear in the foundational JSON yet, treat that as missing curriculum
pressure, not as a failed query.

## Start Here

Get aggregate resource counts first:

```sh
python3 scripts/query-foundational-resources.py summary
```

Then list all packs that advertise a fragment:

```sh
python3 scripts/query-foundational-resources.py packs \
  --fragment QF_LRA \
  --require-any
```

Drill down to checked rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --fragment QF_LRA \
  --proof-status checked \
  --require-any
```

Use `--format json` when another resource index or dashboard needs stable
parsing:

```sh
python3 scripts/query-foundational-resources.py checks \
  --fragment QF_LRA \
  --proof-status checked \
  --format json \
  --limit 5
```

## Core Fragment Lanes

### Bool / CNF

Logic/proof resources with Boolean proof pressure:

```sh
python3 scripts/query-foundational-resources.py packs \
  --fragment Bool \
  --field logic_and_proof \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --fragment Bool \
  --field logic_and_proof \
  --proof-status checked \
  --require-any
```

Use this lane for truth-table resources, small CNF refutations, finite set
families, graph/coloring shadows, and proof-pattern counterexamples.

### QF_BV

Fixed-width arithmetic and residue pressure:

```sh
python3 scripts/query-foundational-resources.py packs \
  --fragment QF_BV \
  --field number_theory \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --fragment QF_BV \
  --field number_theory \
  --proof-status checked \
  --require-any
```

Use this lane only where fixed width is part of the educational claim, such as
finite residues, finite rings/fields, and bit-vector graph encodings.

### QF_LIA

Integer/counting pressure:

```sh
python3 scripts/query-foundational-resources.py packs \
  --fragment QF_LIA \
  --field statistics \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --fragment QF_LIA \
  --field statistics \
  --proof-status checked \
  --require-any
```

Use this lane for Diophantine obstructions, exact counts, contingency-table
totals, bounded induction obligations, graph-search counters, and homology
coefficient checks.

### QF_LRA

Exact-rational pressure:

```sh
python3 scripts/query-foundational-resources.py packs \
  --fragment QF_LRA \
  --field probability_theory \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --fragment QF_LRA \
  --field probability_theory \
  --proof-status checked \
  --require-any
```

Use this lane for probability tables, finite measure/integration, rational
linear systems, LP/Farkas rows, residual bounds, root-finding steps,
optimization iterations, and affine/coordinate geometry.

### QF_UF

Equality and congruence pressure:

```sh
python3 scripts/query-foundational-resources.py packs \
  --fragment QF_UF \
  --field abstract_algebra \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --fragment QF_UF \
  --field abstract_algebra \
  --proof-status checked \
  --require-any
```

Use this lane for finite functions, quotient maps, homomorphism preservation,
monoid/group action laws, ideals, modules, tensors, and table congruence
conflicts.

## Replay And Horizon Lanes

Finite replay pressure:

```sh
python3 scripts/query-foundational-resources.py packs \
  --fragment finite \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --fragment finite \
  --proof-status replay-only \
  --require-any
```

Lean-horizon reconstruction targets:

```sh
python3 scripts/query-foundational-resources.py packs \
  --fragment Lean \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --fragment Lean \
  --proof-status lean-horizon \
  --expected-result not-run \
  --require-any
```

Replay rows and horizon rows are valuable in different ways. Replay rows are
finite trusted resources. Horizon rows identify theorem work that should move
toward Lean or another kernel-checked route.

## Solver-Reuse Drilldowns

Promoted resources by fragment:

```sh
python3 scripts/query-foundational-resources.py packs \
  --fragment QF_LRA \
  --solver-reuse promoted \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --fragment QF_UF \
  --solver-reuse promoted \
  --require-any
```

Use these queries to find candidate source packs for regressions, fuzz seeds,
or benchmark slices. Before making a benchmark or parity claim, follow the
measurement gates in [PLAN.md](../../PLAN.md).

## Frontier Notes

The SMT Fragment Atlas includes frontier rows such as `QF_NRA` and `QF_NIA`.
Those are core solver priorities, but the current foundational-resource public
JSON does not expose a stable `QF_NRA` fragment-demand row through this query
surface. When such rows land, add smoke-checked queries here rather than
silently treating algebraic or Lean-horizon resources as NRA coverage.

This keeps the curriculum corpus honest: demand discovery first, measured
solver parity later.
