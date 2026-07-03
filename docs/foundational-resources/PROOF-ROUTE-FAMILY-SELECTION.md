# Proof Route Family Selection

## Purpose

This file turns the broad proof-upgrade frontier into a compact execution
selection: one replay-heavy family per active evidence route, the current
representative checked row, and the next row shape that should justify another
promotion.

Use this file when choosing the next commit-sized proof-resource increment.
Use [Proof Upgrade Frontier](PROOF-UPGRADE-FRONTIER.md) for the full route
ledger and [Learner And Proof Upgrade Dashboard](generated/learner-proof-upgrade-dashboard.md)
for generated counts.
Use [Proof Upgrade Queries](PROOF-UPGRADE-QUERIES.md) for executable
replay-only row, route-relevant pack, checked-row, and horizon lookups.
The `upgrade-frontier --promotion-state ...` filter is the first stop before a
new promotion: inspect `no-route-contrast` and `partial-route-contrast` before
adding another checked row to a family already marked
`covered-by-route-contrast`.
Use [Proof Route Learner Snippets](../learn/math/proof-route-learner-snippets.md)
when a focused learner page needs compact route wording.

The rule is practical:

```text
do not add another checked row unless it teaches a new proof shape,
trust boundary, solver pressure, or downstream query shape
```

## Current Route Baseline

Audit date: 2026-07-03.

The public query surface reports:

```sh
python3 scripts/query-foundational-resources.py summary
```

- 170 non-template math packs.
- 1110 expected checks.
- 396 checked proof/evidence rows.
- 581 replay-only rows.
- 133 Lean-horizon rows.
- 170 promoted solver-reuse packs.
- 0 non-benchmark-horizon solver-reuse packs.

Route summaries from `scripts/query-foundational-resources.py routes`:

| Route | Packs | Checks | Checked Rows | Replay-Only Rows | Horizon Rows |
|---|---:|---:|---:|---:|---:|
| Boolean CNF/LRAT | 16 | 73 | 52 | 15 | 6 |
| QF_BV bit-blast | 7 | 45 | 34 | 10 | 1 |
| QF_LIA/Diophantine | 15 | 96 | 63 | 25 | 8 |
| QF_LRA/Farkas | 119 | 820 | 216 | 501 | 103 |
| QF_UF/Alethe | 19 | 122 | 58 | 48 | 16 |
| Lean horizon | 140 | 948 | 291 | 524 | 133 |

The counts overlap because packs and rows can carry multiple routes. That is
intentional: a finite topology pack can have finite replay, Boolean evidence,
and Lean-horizon theorem boundaries without conflating them.

## Selected Families

| Route | Representative Family | Current Checked Row | Why This Family | Next Distinct Promotion |
|---|---|---|---|---|
| Boolean CNF/LRAT | finite graph and finite set-family obstruction | `finite-topology-v0` bad empty-open row, plus graph matching/reachability/cut/d-separation rows | Tiny finite objects make the encoder/checker boundary visible: untrusted CNF generation and search, trusted DRAT/LRAT checking. | Add another row only for a learner-readable Boolean shape not covered by pigeonhole, graph reachability/matching/cut/d-separation, finite topology, compactness, connectedness, or lattice top-element rows. |
| QF_BV bit-blast | fixed-width finite algebra and residue search | `finite-fields-v0`, `finite-rings-v0`, `modular-arithmetic-v0`, and graph-coloring fixed-width rows | Width is part of the mathematical object: residues, finite fields/rings, and fixed color encodings should lower through bit-blast evidence. | Add another row only when the bit width is mathematically meaningful and not a disguised finite replay table. |
| QF_LIA/Diophantine | integer obstruction and finite coefficient arithmetic | `gcd-bezout-v0`, `modular-arithmetic-v0`, torsion homology, finite simplicial boundary coefficient and boundary-square cancellation rows, finite graph traversal counters, exact statistical tail/count rows | Integer infeasibility has a compact certificate story: divisibility, gcd obstruction, rank/torsion membership, coefficient cancellation/convolution, or bounded integer counters. | Prefer a new compact obstruction that generalizes across packs, such as another Smith-normal-form/torsion row or a count/margin contradiction that cannot be taught by the existing exact-test rows. |
| QF_LRA/Farkas | exact rational finite-table and optimization conflicts | probability/measure table conflicts including finite total variation, finite covariance entries, conditional-variance decomposition, finite Naive Bayes posterior arithmetic, finite confusion-matrix precision arithmetic, finite ROC/AUC bad-AUC arithmetic, finite precision-recall average-precision arithmetic, finite calibration/Brier-score arithmetic, finite decision-tree weighted-Gini split arithmetic, finite dyadic weighted-entropy split arithmetic, finite nearest-neighbor squared-distance arithmetic, finite perceptron weight-update arithmetic, Schur-complement scalar conflict, finite Euler `qf-lra-*` rows, LP threshold, LU/nullspace, condition-number bound, Jordan nilpotent-component conflict, Newton-coordinate, KKT/SDP/descent/line-search/projected/proximal rows | Farkas is the main exact-rational certificate route and already covers the largest route surface. The best rows start with source replay and then check the linear contradiction. | Add only distinct finite-table or algorithm-step conflicts, not another duplicate product-measure, probability-distance, covariance-entry, classifier-posterior, classifier-metric, ROC/AUC score-ranking, precision-recall average-precision, calibration/Brier-score arithmetic, decision-tree Gini split arithmetic, dyadic weighted-entropy split arithmetic, nearest-neighbor squared-distance arithmetic, perceptron weight-update arithmetic, conditional-moment identity, Schur scalar, Euler table replay, condition-number bound, Jordan component, Newton-coordinate, or generic bound row. |
| QF_UF/Alethe | equality-heavy finite structures and quotient maps | equivalence classes, function composition, finite homomorphisms, finite monoids/groups/actions including permutation injectivity, identity, and compatibility conflicts, finite order-lattice antisymmetry, finite module scalar-closure membership, finite vector-space additive-closure membership, finite dual-space covector additivity, finite tensor-product left-additivity, continuous-map preimage membership, quotient topology representative/open conflicts, and cohomology shadows | Alethe adds value when table replay says what happened and congruence proof explains why an equality claim is impossible. | Prefer equality conflicts where table replay and congruence proof teach different things, such as algebra/topology map preservation beyond the current preimage, order/lattice relation consistency beyond the current antisymmetry row, module/vector-space/dual-space/tensor closure or additivity, and quotient representative consistency rows. |
| Lean horizon | theorem boundary families | induction schemas, completeness, compactness, convergence, measure limits, general algebra, Banach/Hilbert/Jordan/Chebyshev facts, and Schur/block-inverse theorem boundaries | These rows keep finite shadows honest. They should state theorem shape and missing proof dependencies, not masquerade as SMT evidence. | Add or split horizon rows when a learner page risks overclaiming from a bounded example or when a future Lean reconstruction target needs prerequisites named. |

## Promotion Discipline

Before promoting another compact negative row to checked evidence:

1. Name the source family and the exact finite object.
2. Show why existing checked rows do not already teach the same proof shape.
3. Keep satisfiable rows on finite replay unless a certificate route adds
   meaningful assurance.
4. Link the pack to the proof cookbook recipe and the recipe back to at least
   one math example.
5. Add a route-specific regression or source artifact only after replay is
   deterministic.
6. Keep theorem-horizon rows out of benchmark or solver-performance claims.

## Query Commands

Route-level summaries:

```sh
python3 scripts/query-foundational-resources.py routes --route "CNF"
python3 scripts/query-foundational-resources.py routes --route "qf-bv"
python3 scripts/query-foundational-resources.py routes --route "Diophantine"
python3 scripts/query-foundational-resources.py routes --route "Farkas"
python3 scripts/query-foundational-resources.py routes --route "Alethe"
python3 scripts/query-foundational-resources.py routes --route "Lean"
```

Field-scoped examples:

```sh
python3 scripts/query-foundational-resources.py routes --field graph_theory
python3 scripts/query-foundational-resources.py routes --field linear_algebra
python3 scripts/query-foundational-resources.py routes --field probability_theory
python3 scripts/query-foundational-resources.py routes --field topology
```

Use `--format json` when a downstream consumer needs machine-readable route
rows.

Replay-only `unsat` rows grouped by certificate route:

```sh
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas
python3 scripts/query-foundational-resources.py upgrade-frontier --route Alethe
python3 scripts/query-foundational-resources.py upgrade-frontier --route qf-bv
python3 scripts/query-foundational-resources.py upgrade-frontier --route Diophantine
```

Promotion-state triage:

```sh
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas --promotion-state no-route-contrast --format json
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas --promotion-state partial-route-contrast --format json
python3 scripts/query-foundational-resources.py upgrade-frontier --route Alethe --promotion-state covered-by-route-contrast --require-any
```

This frontier query is a selection aid, not an automatic promotion queue. A
row should still be promoted only when it teaches a new proof shape, trust
boundary, solver pressure, or downstream query shape.

## Validation

For a docs-only selection update:

```sh
python3 scripts/query-foundational-resources.py summary
./scripts/check-foundational-resources.sh
./scripts/check-links.sh
```

For a real proof-route promotion, add the route-specific cargo test named in
[Proof Upgrade Frontier](PROOF-UPGRADE-FRONTIER.md) and validate the affected
pack with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>
```

The promotion is not complete until the artifact or regression rejects a
tampered or missing certificate where the route supports tamper rejection.
Use [Checker Tamper Matrix](CHECKER-TAMPER-MATRIX.md) to find the current
focused corrupted-evidence command, and keep unsupported tamper routes explicit
as gaps.
