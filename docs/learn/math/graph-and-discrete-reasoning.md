# Graph And Discrete Reasoning

Concept rows:

- `field_graph_theory`, `field_discrete_math`, and `field_logic_and_proof` in
  the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_finite_counting_replay` and
  `bridge_finite_graph_replay_obstruction` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_counting`, `curriculum_sets`, and
  `curriculum_relations_and_functions` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [counting-v0](../../../artifacts/examples/math/counting-v0/)
- [generating-functions-v0](../../../artifacts/examples/math/generating-functions-v0/)
- [finite-recurrence-prefix-v0](../../../artifacts/examples/math/finite-recurrence-prefix-v0/)
- [finite-permutation-groups-v0](../../../artifacts/examples/math/finite-permutation-groups-v0/)
- [finite-group-actions-v0](../../../artifacts/examples/math/finite-group-actions-v0/)
- [graph-coloring-v0](../../../artifacts/examples/math/graph-coloring-v0/)
- [graph-reachability-v0](../../../artifacts/examples/math/graph-reachability-v0/)
- [graph-search-runtime-v0](../../../artifacts/examples/math/graph-search-runtime-v0/)
- [graph-matching-v0](../../../artifacts/examples/math/graph-matching-v0/)
- [graph-d-separation-v0](../../../artifacts/examples/math/graph-d-separation-v0/)
- [graph-cut-v0](../../../artifacts/examples/math/graph-cut-v0/)
- [proof-methods-refutation-v0](../../../artifacts/examples/math/proof-methods-refutation-v0/)

Companion map:

- [Graph Traversal Runtime Index](graph-traversal-runtime-index.md)

## What Axeyum Checks

The discrete path starts with finite counting and graph coloring. The counting
pack checks fixed permutation and binomial counts, then exhaustively rejects an
injection from three pigeons into two holes. The generating-functions pack
checks finite coefficient extraction, Cauchy product convolution, a bounded
Fibonacci generating-function identity, and a bad convolution coefficient. The
finite-recurrence-prefix pack checks Fibonacci and affine recurrence prefixes,
plus a companion-matrix state trace, rejects malformed finite Fibonacci and
affine-step source rows by exact replay, and exposes separate checked
QF_LRA/Farkas proof rows. The
finite-permutation-groups pack adds symmetry data: it checks `S3` as bijective
function tables, recomputes cycle lengths and parity signs, and replays the
natural action's orbit and stabilizer. The finite-group-actions pack adds
finite orbit counting: it checks action laws, recomputes orbits and
stabilizers, and verifies Burnside's fixed-point average for one small action.
The graph coloring pack replays a
coloring witness against every edge, rejects an invalid coloring, and checks a
tiny `K3` two-colorability refutation by exhaustive finite search. The graph
reachability pack checks finite BFS distances, deterministic DFS traversal
order, disconnected no-path claims, and edge-cut separation. The graph search
runtime pack adds finite visited-node counters for BFS and DFS target discovery,
checks a shortcut-tail family, and rejects a false DFS cost bound with a
checked QF_LIA arithmetic-DPLL regression. The graph
matching pack checks finite matching witnesses, invalid overlapping edges,
augmenting path flips, and a perfect-matching obstruction. The DAG
d-separation pack checks chains, forks, colliders, and descendant-opened
colliders by enumerating finite skeleton paths, with CNF/DRAT/LRAT artifacts for
conditioned-chain and unconditioned-collider blockers. The graph cut pack checks
minimum edge and vertex cut certificates by replaying separation and
enumerating smaller candidate cuts.

This gives a direct model of "untrusted fast search, trusted small checking":
the search can propose colors, but the checker only needs the graph and the
candidate assignment. For traversal, the search can propose a path or trace,
but the checker recomputes reachability from the raw finite graph. For
traversal cost, the search can propose visited-count counters, but the checker
recomputes BFS pop order and DFS preorder from deterministic adjacency. For
matching, the search can propose edges or an augmenting path; the checker
verifies disjoint endpoints and enumerates the small matching space when a
maximum or obstruction is claimed. For d-separation, the search can propose an
active path, but the checker recomputes every simple path and applies the
collider/non-collider blocking rules. For cuts, the search can propose a cut
set and a partition; the checker removes edges or vertices, recomputes
reachability, and enumerates smaller cuts.
The shared `bridge_finite_graph_replay_obstruction` row is the atlas vocabulary
for this finite graph pattern across coloring, reachability, traversal,
matching, cut, and d-separation resources. It is deliberately finite: graph
minors, max-flow/min-cut theorems, matching duality, causal identification,
and asymptotic traversal complexity stay in proof-horizon resources.

## Encode / Check Walkthrough

For counting, encode fixed integers:

```text
n = 6
k = 3
C(6,3) = C(5,2) + C(5,3)
20 = 10 + 10
```

For pigeonhole, the validator enumerates every placement of three pigeons into
two holes and confirms every placement has a collision.

For generating functions, encode finite ordinary generating polynomials as
coefficient lists:

```text
A(x) = 1 + 2*x + x^2
B(x) = 1 + x + x^2
A(x)B(x) = 1 + 3*x + 4*x^2 + 3*x^3 + x^4
```

The `generating-functions-v0` pack recomputes the Cauchy convolution exactly.
It also checks a bounded Fibonacci prefix identity for
`(1 - x - x^2)F(x) = x` through a fixed degree and rejects a product with one
bad coefficient through a checked QF_LIA/Diophantine certificate.

For finite recurrence prefixes, encode the sequence table directly:

```text
F = [0, 1, 1, 2, 3, 5, 8]
x = [0, 1, 3, 7, 15]  where x_{n+1} = 2*x_n + 1
```

The `finite-recurrence-prefix-v0` pack recomputes each prefix and the
Fibonacci companion-matrix trace. Its malformed source rows reject `F_6 = 9`
after replay computes `F_6 = 8`, and reject `x_4 = 14` after affine recurrence
replay computes `x_4 = 15`; separate `qf-lra-*` rows own the checked proof
artifacts.

For orbit counting,
first encode finite permutations as bijections:

```text
S3 acts on {1,2,3}
r = (1 2 3)
s23 = (2 3)
r after s23 = s12
cycle_lengths(r) = [3]
sign(s23) = odd
stabilizer(1) = {e, s23}
```

The `finite-permutation-groups-v0` pack recomputes the composition table from
the permutation maps, checks cycle/sign data, and verifies the natural action's
orbit-stabilizer count. Then encode a finite group action and fixed-point
counts:

```text
C2 = {e,s}
points = 00, 01, 10, 11
s swaps 01 and 10
s fixes 00 and 11
fixed(e) = 4
fixed(s) = 2
orbit count = (4 + 2) / 2 = 3
```

The `finite-group-actions-v0` pack recomputes the action orbits
`{00}`, `{01,10}`, and `{11}` and checks the Burnside average exactly, while
exact replay rejects malformed identity and compatibility action tables before
the explicit QF_UF/Alethe rows check the isolated equality conflicts.

For graph coloring,
encode a finite graph by listing vertices, undirected edges, allowed colors, and
one assignment:

```text
vertices = a,b,c
edges = (a,b), (b,c), (a,c)
colors = red, green, blue
assignment = a:red, b:green, c:blue
```

The validator replays the assignment by checking that every edge has different
endpoint colors. For the two-colorability refutation of `K3`, the pack fixes
the same triangle with two colors and the validator exhaustively enumerates the
finite assignment space.

For reachability and traversal, encode the graph once and replay both BFS and
DFS facts against it:

```text
vertices = s, a, b, c, d, t
edges = (s,a), (a,b), (b,c), (c,d), (d,t), (s,t)
BFS shortest path = s, t
DFS order = s, a, b, c, d, t
```

The direct edge makes the BFS distance from `s` to `t` equal to `1`, while the
deterministic DFS order walks the long tail first. The validator recomputes the
distance map and the traversal order instead of trusting either list.

For traversal runtime counters, use the shortcut-tail family. The checked slice
is finite cost replay, not a general complexity theorem:

```text
vertices = s, a1, a2, a3, a4, t
edges = (s,a1), (s,t), (a1,a2), (a2,a3), (a3,a4)
BFS pop order until t = s, a1, t
DFS preorder until t = s, a1, a2, a3, a4, t
BFS visited count = 3
DFS visited count = 6
```

The family rows for tail lengths `2`, `4`, and `8` keep the BFS visited count
at `3` while the deterministic DFS visited count grows to `4`, `6`, and `10`.
The validator generates each listed graph and rejects a false claim that DFS on
the length-four graph reaches `t` within three visits.

For matching, list graph edges and the chosen matching:

```text
vertices = a, b, c, d
edges = (a,b), (b,c), (c,d)
matching = (a,b), (c,d)
augmenting path from current matching (b,c) = a, b, c, d
```

The validator checks that matching edges are real graph edges with no shared
endpoints. For the augmenting path it checks unmatched endpoints, alternating
matched/unmatched edges, and the exact flip to `(a,b), (c,d)`.

For d-separation, encode a finite DAG and a conditioning set:

```text
chain: a -> b -> c
conditioning set = {b}
query = is a d-connected to c?
```

Conditioning on the middle non-collider blocks the chain. In contrast:

```text
collider: a -> b <- c, b -> d
conditioning set = {d}
```

opens the path through `b` because `d` is a descendant of the collider.
The pack also refutes the unconditioned collider `a -> b <- c` with no
conditioning through a tiny source-linked CNF artifact checked by DRAT and LRAT.

For cut certificates, encode a finite graph, a source/target pair, and the
proposed cut:

```text
vertices = s, a, b, t
edges = (s,a), (a,t), (s,b), (b,t)
edge cut = (s,a), (s,b)
source side = {s}
target side = {a,b,t}
```

The validator checks that the cut edges are exactly the partition crossing
edges, removes them, confirms `t` is unreachable from `s`, and enumerates all
one-edge removals to justify the minimum size.

Run the check from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/counting-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/generating-functions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-recurrence-prefix-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_recurrence_prefix_bad_value_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-permutation-groups-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-group-actions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-reachability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-search-runtime-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-matching-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-d-separation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-cut-v0
```

For a fuller trace from data row to replay result and evidence status, read
[End To End: Counting And Pigeonhole](counting-pigeonhole-end-to-end.md),
[End To End: Triangle Coloring](graph-coloring-end-to-end.md),
[End To End: Graph Reachability And Traversal](graph-reachability-end-to-end.md),
[End To End: Graph Search Runtime Counters](graph-search-runtime-end-to-end.md),
[End To End: Graph Matching And Augmenting Paths](graph-matching-end-to-end.md),
[End To End: Graph Cut Certificates](graph-cut-end-to-end.md),
[End To End: DAG D-Separation Checks](graph-d-separation-end-to-end.md),
[End To End: Finite Permutation Groups](finite-permutation-groups-end-to-end.md), and
[End To End: Finite Group Actions And Burnside Counting](finite-group-actions-end-to-end.md).
For coefficient-level finite recurrence and convolution replay, read
[End To End: Generating Functions](generating-functions-end-to-end.md). For
finite recurrence-prefix and companion-matrix replay, read
[End To End: Finite Recurrence Prefixes](finite-recurrence-prefix-end-to-end.md).

## Proof Upgrade Notes

Finite witnesses for colors, paths, traversal orders, matchings, cuts, or
coefficient lists stay on
[Finite Model Replay](../../proof-cookbook/recipes/finite-model-replay.md):
the checker recomputes the finite graph or polynomial claim from the source
data. Boolean impossibility claims such as pigeonhole and graph non-colorability
should use
[Boolean CNF DRAT/LRAT Evidence](../../proof-cookbook/recipes/boolean-cnf-lrat.md)
once a deterministic CNF is the source artifact. Fixed-width graph encodings,
such as the one-bit triangle two-coloring obstruction, belong to
[QF_BV Bit-Blast Evidence](../../proof-cookbook/recipes/qf-bv-bitblast.md)
only when the finite width is part of the lesson. Traversal-cost counters and
finite counting equalities can graduate through checked LIA evidence. Pure
integer-equality obstructions use
[QF_LIA / Diophantine Evidence](../../proof-cookbook/recipes/qf-lia-diophantine.md)
while Boolean-structured LIA rows, such as the bad DFS cost bound, are pinned by
resource regressions that independently recheck arithmetic-DPLL evidence.
Asymptotic runtime, extremal graph theory, and closed-form combinatorics remain
[Lean Horizon](../../proof-cookbook/recipes/lean-horizon-template.md) targets.

## Horizon

The fixed pigeonhole refutation is checked by finite enumeration and now also
has source-linked DRAT/LRAT evidence for its DIMACS artifact. Finite
permutation cycle/sign data, finite group-action orbit counts, reachability,
traversal traces, finite traversal-cost counters, matching, d-separation, and
cut certificates now have dedicated finite packs. General permutation-group theory,
Burnside/orbit-stabilizer theory, closed-form generating-function extraction,
weighted max-flow/min-cut, extremal graph theory, graph minors, asymptotic
graph families, causal identification, average-case search, parallel search,
and runtime-pathology proofs need theorem-proving support beyond the current
finite examples.
