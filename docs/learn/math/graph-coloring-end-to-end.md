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
| `triangle-not-2-colorable-qf-bv-drat` | `unsat` | checked DRAT |

The first check is a model witness. The last two checks are refutations of
specific finite claims. The triangle non-2-colorability row now also has a
resource-backed CNF proof regression that emits and checks DRAT, then elaborates
and checks LRAT. The QF_BV row gives the same finite obstruction a separate
fixed-width encoding: one 1-bit color per vertex, with checked DRAT over the
bit-blasted CNF.

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

The CNF proof route uses one Boolean variable per vertex: true means `red`,
false means `blue`. Each edge contributes two clauses, `(u or v)` and
`(not u or not v)`, so endpoints must differ. For the triangle this produces
the DIMACS artifact
[`triangle-not-2-colorable.cnf`](../../../artifacts/examples/math/graph-coloring-v0/cnf/triangle-not-2-colorable.cnf).
The proof-producing SAT core is untrusted search; the accepted evidence is the
independent DRAT check and the elaborated LRAT check.

The QF_BV proof route uses one 1-bit bit-vector variable per vertex instead of
raw DIMACS variables:

```text
a != b
b != c
a != c
```

Those three constraints assert that three triangle vertices have pairwise
different values in a two-value domain. The SMT-LIB artifact
[`triangle-not-2-colorable-bitblast-conflict.smt2`](../../../artifacts/examples/math/graph-coloring-v0/smt2/triangle-not-2-colorable-bitblast-conflict.smt2)
is parsed by the resource regression, bit-blasted to CNF, refuted with DRAT,
and rechecked from the saved certificate text.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes graph_coloring_triangle_not_2_colorable_emits_checked_drat_and_lrat
cargo test -p axeyum-solver --test math_resource_bv_routes graph_coloring_triangle_not_2_colorable_emits_checked_bv_drat
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

For the finite `unsat` rows, exhaustive enumeration remains the pack validator.
The triangle non-2-colorability row also exercises a SAT/CNF encoding and small
checked DRAT/LRAT proof path using the
[Boolean CNF DRAT/LRAT Evidence](../../proof-cookbook/recipes/boolean-cnf-lrat.md)
recipe, plus a fixed-width BV encoding using the
[QF_BV Bit-Blast Evidence](../../proof-cookbook/recipes/qf-bv-bitblast.md)
recipe. In the BV route, graph-to-BV lowering and bit-blast/Tseitin lowering
remain explicit trust steps until Lean reconstruction covers the original
formula directly.
