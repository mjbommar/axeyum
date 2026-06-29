# End To End: Finite Cardinality

This lesson follows one finite cardinality resource from explicit function
graphs to replayed result and proof/evidence status. It uses the
[finite-cardinality-v0](../../../artifacts/examples/math/finite-cardinality-v0/)
pack.

Concept rows:

- `curriculum_cardinality`, `curriculum_relations_and_functions`, and
  `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_set_theory_and_foundations` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `finite-bijection-cardinality-witness` | `sat` | checked |
| `proper-subset-injection-witness` | `sat` | checked |
| `no-injection-four-to-three` | `unsat` | checked |
| `no-surjection-two-to-three` | `unsat` | checked |
| `cantor-diagonal-lean-horizon` | `not-run` | lean-horizon |

The checked rows are finite function-graph rows. The pack does not claim
countability, uncountability, Schroeder-Bernstein, or infinite cardinal
arithmetic.

## Encode

The pack represents finite functions as explicit graph data:

```text
domain = finite input labels
codomain = finite output labels
pairs = [input, output] graph entries
```

The validator checks the graph itself:

```text
total:         every domain element has an output
single-valued: no domain element has two outputs
injective:     no two inputs share the same output
surjective:    every codomain element is hit
bijective:     injective and surjective
```

It does not trust labels like "bijection" or "proper subset" unless the listed
finite data proves them.

## Replay Equal Cardinality

The first witness maps three domain elements to three codomain elements:

```text
a -> 1
b -> 2
c -> 0
```

The checker verifies the graph is total and single-valued:

```text
a, b, c each appear exactly once as inputs
```

It then verifies injectivity and surjectivity:

```text
outputs = {1, 2, 0}
codomain = {0, 1, 2}
```

Because every codomain element is hit exactly once, the graph is a bijection
and witnesses equal finite cardinality.

## Replay A Proper-Subset Injection

The second witness maps a two-element subset into a three-element set:

```text
domain = {alpha, beta}
codomain = {alpha, beta, gamma}

alpha -> alpha
beta  -> beta
```

The checker verifies the map is injective:

```text
alpha and beta have distinct outputs
```

It also checks that the map is not surjective:

```text
gamma is not hit
```

So the row witnesses the finite inequality `2 < 3` using explicit function
data.

## Check Finite Refutations By Enumeration

The no-injection row asks for an injective function from four elements to
three elements:

```text
domain size = 4
codomain size = 3
function count = 3^4 = 81
```

The validator enumerates all `81` functions and confirms none is injective.

The no-surjection row asks for a surjective function from two elements onto
three elements:

```text
domain size = 2
codomain size = 3
function count = 3^2 = 9
```

The validator enumerates all `9` functions and confirms none hits all three
codomain elements.

These are finite checked refutations. They are not proofs about arbitrary
finite sizes unless the size parameters are also encoded and proved.

## Name The Infinite Horizon

The Cantor row records the theorem shape:

```text
there is no surjection from N onto P(N)
```

The pack deliberately marks it `not-run` and `lean-horizon`. A finite function
enumeration cannot prove this infinite theorem; it needs a proof-assistant
route.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cardinality-v0
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite cardinality:

```text
untrusted fast search -> candidate finite function graph
trusted small checking -> totality, injectivity, surjectivity, finite enumeration
```

Infinite cardinality, countability, Cantor diagonalization, Schroeder-Bernstein,
and cardinal arithmetic require stronger proof routes or Lean/mathlib-scale
proof support.
