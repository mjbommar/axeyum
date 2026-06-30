# End To End: Finite Simplicial Cup Products

This lesson follows one finite algebraic-topology resource from ordered
simplices and F2 cochain tables to a cup-product replay and a checked bad-value
counterexample. It uses
[finite-simplicial-cup-products-v0](../../../artifacts/examples/math/finite-simplicial-cup-products-v0/).

Concept rows:

- `bridge_finite_cup_product_replay`,
  `bridge_finite_cohomology_replay`,
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
| `cup-product-replay` | `sat` | replay-only |
| `cup-coboundary-leibniz-replay` | `sat` | replay-only |
| `bad-cup-product-rejected` | `unsat` | checked |
| `qf-bv-bad-cup-product` | `unsat` | checked |
| `general-cup-product-lean-horizon` | `not-run` | lean-horizon |

Every replay row is finite simplex and F2 cochain arithmetic. The checked
solver row is a fixed one-bit QF_BV contradiction after replay computes the
cup-product value. The pack does not prove associativity, graded commutativity,
naturality, cohomology-ring quotienting, or topological invariance.

## Encode The Cup Product

The first witness uses the filled triangle:

```text
simplices = [a], [b], [c], [a,b], [a,c], [b,c], [a,b,c]
vertex order = a < b < c
```

It lists two 1-cochains over `F2`:

```text
alpha([a,b]) = 1   beta([a,b]) = 0
alpha([a,c]) = 0   beta([a,c]) = 0
alpha([b,c]) = 0   beta([b,c]) = 1
```

The finite checker uses the Alexander-Whitney split:

```text
(alpha cup beta)([v0,...,v(p+q)])
  = alpha([v0,...,vp]) * beta([vp,...,v(p+q)]) mod 2
```

So for the triangle:

```text
(alpha cup beta)([a,b,c]) = alpha([a,b]) * beta([b,c]) = 1
(beta cup alpha)([a,b,c]) = beta([a,b]) * alpha([b,c]) = 0
```

That order dependence is a cochain-level finite computation, not a general
graded-commutativity theorem.

## Replay One Leibniz Row

The second witness uses two 0-cochains:

```text
f(a)=1, f(b)=0, f(c)=1
g(a)=1, g(b)=1, g(c)=0
```

The validator recomputes:

```text
f cup g
delta f
delta g
delta(f cup g)
delta f cup g
f cup delta g
```

and checks the finite F2 row:

```text
delta(f cup g) = delta(f) cup g + f cup delta(g)
```

The result is replay for this listed table. The general Leibniz rule over all
cochain degrees and complexes remains a theorem-horizon target.

## Reject A Bad Cup Product

The negative row claims:

```text
(alpha cup beta)([a,b,c]) = 0
```

Finite replay computes:

```text
alpha([a,b]) * beta([b,c]) = 1 * 1 = 1
```

so the row is rejected.

## Check The Bit-Blast Certificate

The solver-form row isolates the same mismatch as one-bit arithmetic:

```text
alpha_ab = 1
beta_bc = 1
cup_abc = alpha_ab AND beta_bc
cup_abc = 0
```

Axeyum bit-blasts that fixed QF_BV conflict, emits DRAT evidence for the CNF,
and rechecks the proof. The trusted claim is the small checked CNF refutation
plus the finite replay that exposed the one-bit conflict.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-cup-products-v0
cargo test -p axeyum-solver --test math_resource_bv_routes finite_simplicial_cup_product_bad_value_emits_checked_bv_drat
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

```text
untrusted fast search -> candidate cochain operation or bad cup-product value
trusted small checking -> finite F2 cup-product replay and checked QF_BV/DRAT value proof
remaining horizon -> associativity, graded commutativity, naturality, cohomology rings, and invariance
```

For the coboundary and cohomology-rank side of the same finite complex style,
read
[End To End: Finite Simplicial Cohomology](finite-simplicial-cohomology-end-to-end.md).
