# End To End: Finite Simplicial Cohomology

This lesson follows one finite algebraic-topology resource from cochain tables
to coboundary replay and a checked bad-value counterexample. It uses
[finite-simplicial-cohomology-v0](../../../artifacts/examples/math/finite-simplicial-cohomology-v0/).

Concept rows:

- `bridge_finite_cohomology_replay`,
  `bridge_finite_boundary_operator_replay`, and
  `bridge_finite_chain_homology_replay` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_sets`, `curriculum_relations_and_functions`, and
  `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_topology`, `field_set_theory_and_foundations`,
  `field_linear_algebra`, and `field_abstract_algebra` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `coboundary-replay` | `sat` | replay-only |
| `coboundary-squared-zero` | `sat` | replay-only |
| `cohomology-rank-replay` | `sat` | replay-only |
| `bad-coboundary-rejected` | `unsat` | checked |
| `qf-uf-bad-coboundary-value` | `unsat` | checked |
| `general-cohomology-lean-horizon` | `not-run` | lean-horizon |

Every replay row is finite simplex and F2 cochain arithmetic. The checked
solver row is a fixed QF_UF/Alethe equality contradiction after replay computes
the coboundary value. The pack does not prove cohomology functoriality, cup
product laws, cohomology rings, universal coefficients, duality, de Rham
comparison, or invariance. The next finite cochain operation is covered by
[End To End: Finite Simplicial Cup Products](finite-simplicial-cup-products-end-to-end.md).

## Encode The Cochain

The first witness uses the three-edge circle:

```text
simplices = [a], [b], [c], [a,b], [a,c], [b,c]
```

and the 0-cochain:

```text
f(a) = 0
f(b) = 1
f(c) = 0
```

Over `F2`, signs disappear, so the coboundary on an edge is the sum of endpoint
values modulo `2`:

```text
delta f([a,b]) = 1
delta f([a,c]) = 0
delta f([b,c]) = 1
```

The validator recomputes those values from the listed simplices and cochain
table.

## Check Delta Squared

The filled triangle adds the 2-simplex:

```text
[a,b,c]
```

The first coboundary is still:

```text
delta f([a,b]) = 1
delta f([a,c]) = 0
delta f([b,c]) = 1
```

Applying `delta` again sums the three edge values on the triangle:

```text
1 + 0 + 1 = 0 mod 2
```

So the listed second coboundary is the zero 2-cochain. This is one finite
cochain-complex replay, not a general proof about all complexes.

## Replay Cohomology Dimensions

For the three-edge circle, the validator builds finite coboundary matrices over
`F2`:

```text
dim C0 = 3
dim C1 = 3
dim C2 = 0
rank delta0 = 2
rank delta1 = 0
```

Then it checks:

```text
h0 = dim ker delta0 - rank delta(-1) = (3 - 2) - 0 = 1
h1 = dim ker delta1 - rank delta0  = (3 - 0) - 2 = 1
```

The all-ones 1-cochain:

```text
phi([a,b]) = phi([a,c]) = phi([b,c]) = 1
```

is a cocycle because there are no 2-simplices. The validator also checks it is
not a coboundary by enumerating the eight possible 0-cochains.

## Reject A Bad Coboundary Value

The negative row claims:

```text
delta f([a,c]) = 1
```

Finite replay computes:

```text
delta f([a,c]) = f(a) + f(c) = 0 + 0 = 0
```

The source SMT-LIB artifact isolates the final mismatch as:

```text
delta_ac = zero
delta_ac = one
zero != one
```

Axeyum emits `UnsatAletheProof` evidence for that fixed equality conflict, and
`Evidence::check` independently rechecks it.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-cohomology-v0
cargo test -p axeyum-solver --test math_resource_uf_routes finite_simplicial_cohomology_bad_coboundary_value_emits_checked_alethe
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate cochain table or bad coboundary value
trusted small checking -> finite F2 coboundary replay and checked Alethe value proof
remaining horizon -> general cup-product laws, cohomology rings, functoriality, duality, and invariance
```

For the boundary and homology side of the same finite complex style, read
[End To End: Finite Simplicial Homology](finite-simplicial-homology-end-to-end.md).
For the integer Hom/Ext shadow that connects torsion homology to cohomology,
read
[End To End: Finite Universal Coefficient Shadow](finite-universal-coefficient-shadow-end-to-end.md).
For the finite cup-product operation on cochains, read
[End To End: Finite Simplicial Cup Products](finite-simplicial-cup-products-end-to-end.md).
