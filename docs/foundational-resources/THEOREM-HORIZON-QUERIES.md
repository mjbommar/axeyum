# Theorem Horizon Queries

This is the consumer-facing query guide for Lean/theorem-horizon rows. It is
the companion to the proof-route summary in
[Proof Route Query Matrix](PROOF-ROUTE-QUERY-MATRIX.md) and the learner-facing
[Lean Horizon](../proof-cookbook/recipes/lean-horizon-template.md) recipe.

The horizon rows are deliberately negative claims about current evidence:

```text
finite check exists -> useful bounded shadow
general theorem     -> not proved here yet; needs Lean/theorem reconstruction
```

Use this guide when a consumer wants to find which mathematical claims are
explicitly out of scope for the current finite resource and should not be
treated as SMT, replay, benchmark, or solver-parity evidence.

## Start Here

Summarize the Lean-horizon route:

```sh
python3 scripts/query-foundational-resources.py routes \
  --route lean \
  --require-any
```

Find packs that declare the route:

```sh
python3 scripts/query-foundational-resources.py packs \
  --route lean-horizon-template \
  --proof-status lean-horizon \
  --require-any
```

Find the actual horizon rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --proof-status lean-horizon \
  --require-any
```

Pack route summaries use the recipe name `lean-horizon-template`; individual
row discovery should usually filter by `--proof-status lean-horizon`, because
horizon rows are metadata rows rather than checked proof-object rows.

## Field-Scoped Horizon Queries

Logic and proof horizons:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field logic_and_proof \
  --proof-status lean-horizon \
  --require-any
```

Topology and algebraic-topology horizons:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field topology \
  --route lean-horizon-template \
  --proof-status lean-horizon \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field topology \
  --proof-status lean-horizon \
  --require-any
```

Real-analysis and optimization horizons:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field real_analysis \
  --proof-status lean-horizon \
  --require-any
```

Measure/probability horizons:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field measure_theory \
  --proof-status lean-horizon \
  --require-any
```

Graph/asymptotic horizons:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --proof-status lean-horizon \
  --require-any
```

Convergence horizons across fields:

```sh
python3 scripts/query-foundational-resources.py checks \
  --text convergence \
  --proof-status lean-horizon \
  --require-any
```

## Read With The Learner Maps

The main learner maps that explain these boundaries are:

- [Analysis And Calculus Theorem Horizon Map](../learn/math/analysis-calculus-theorem-horizon-map.md)
- [Real Completeness Theorem Boundary](../learn/math/real-completeness-theorem-boundary.md)
- [Analysis And Topology Proof Horizons](../learn/math/analysis-topology-proof-horizons.md)
- [Matrix Corpus And Benchmark Boundary](../learn/math/matrix-corpus-benchmark-boundary.md)
- [Finite Countermodel Replay](../learn/math/finite-countermodel-replay.md)

Those pages state the finite or computable slice first, then name the missing
general theorem route. This is the intended reading order: bounded check before
horizon.

## Boundary

A horizon row proves neither the theorem nor its negation. It is a resource
boundary marker. Consumers may use it to:

- warn that a finite example does not prove a general theorem;
- route future work toward Lean or another kernel-checked theorem path;
- keep theorem claims out of solver-performance and benchmark summaries;
- explain why a pack contains `not-run` rows alongside checked finite rows.

Do not count Lean-horizon rows as checked SMT evidence, checked replay
evidence, or parity with Z3/cvc5/Lean. They are explicit work items for future
proof reconstruction.
