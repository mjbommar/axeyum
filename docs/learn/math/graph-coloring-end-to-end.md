# End To End: Triangle Coloring

This lesson follows one validated resource from data row to replay result and
proof/evidence status. It uses the
[graph-coloring-v0](../../../artifacts/examples/math/graph-coloring-v0/) pack.

Concept rows:

- `field_graph_theory`, `field_discrete_math`, and `field_logic_and_proof` in
  the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_counting` and `curriculum_propositional_logic` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

## Claim Shape

There are three checks in the pack:

| Check | Expected | Evidence Status |
|---|---|---|
| `triangle-3-coloring-witness` | `sat` | replay-only |
| `bad-edge-coloring-rejected` | `unsat` | checked |
| `triangle-not-2-colorable` | `unsat` | checked |

The first check is a model witness. The last two checks are refutations of
specific finite claims. The pack does not yet emit CNF or LRAT/DRAT proof
artifacts.

## Encode

The `sat` witness is plain finite data:

```text
vertices = a,b,c
edges = (a,b), (b,c), (a,c)
colors = red, green, blue
assignment = a:red, b:green, c:blue
```

The trusted checker does not need to solve the problem again. It only needs to
replay the proposed model against the original graph.

## Replay The Model

For each edge, compare endpoint colors:

| Edge | Endpoint Colors | Passes |
|---|---|---|
| `(a,b)` | `red`, `green` | yes |
| `(b,c)` | `green`, `blue` | yes |
| `(a,c)` | `red`, `blue` | yes |

Every edge passes, so the `triangle-3-coloring-witness` check is `sat` with a
replayed witness.

## Check The Refutations

The invalid-witness check encodes a one-edge graph where both endpoints are
`red`. The checker recomputes the only edge constraint and rejects the claim
that this is a proper coloring.

The two-colorability refutation fixes `K3` and two colors. There are only
`2^3 = 8` assignments, so the validator enumerates all of them and confirms
that each assignment has at least one monochromatic edge.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This is the core Axeyum pattern:

```text
untrusted fast search -> candidate coloring
trusted small checking -> edge-by-edge replay
```

For the finite `unsat` rows, the current trusted checker is exhaustive
enumeration. The next graduation step is to add a SAT/CNF encoding and a small
checked proof artifact for non-colorability claims, then link that proof recipe
from the proof cookbook.
