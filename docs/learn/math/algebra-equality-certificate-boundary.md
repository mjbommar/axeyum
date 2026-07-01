# Algebra Equality Certificate Boundary

This page is for the algebra queue item:

```text
Add equality/certificate rows only when table replay and congruence proof tell different useful stories.
```

Finite algebra rows start as exact table replay. A checked QF_UF/Alethe row is
worth adding only when it isolates a reusable equality proof shape that the
table replay does not already explain by itself.

The trust split is:

```text
untrusted fast search -> candidate map, subset, quotient table, or malformed row
trusted replay -> finite table evaluation finds the exact failing equation
trusted certificate -> QF_UF/Alethe checks the isolated equality conflict
theorem horizon -> arbitrary algebraic structure theorems and universal properties
```

## Concept Rows

- `bridge_algebra_equality_certificate_boundary`
- `family_finite_algebra_alethe`
- `bridge_homomorphism_preservation`
- `bridge_kernel_image`
- `bridge_quotient_map`
- `bridge_ideal_closure`
- `bridge_group_action`
- `bridge_module_action`
- `bridge_tensor_bilinearity`

These rows live in the
[Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json).

## Promotion Rule

Do not add an algebra certificate just because a pack is algebraic. Add one
only when all five checks pass:

1. The finite model is already explicit: operation table, function table,
   subset, quotient representatives, module action, or bilinear map.
2. Exact replay identifies a small equality, congruence, closure,
   representative-independence, preservation, identity-action, or bilinearity
   conflict.
3. The SMT-LIB artifact isolates that conflict as QF_UF rather than smuggling
   the whole table checker into the solver.
4. `math_resource_uf_routes` emits `UnsatAletheProof` and rechecks it through
   `Evidence::check`.
5. The learner text says exactly what remains theorem horizon.

If the row fails one of these tests, keep it as replay-only or mark the theorem
route explicitly instead.

## Current Equality Certificate Map

| Pack | Replay Story | Certificate Story | Horizon |
|---|---|---|---|
| `finite-groups-v0` | Cayley-table closure, identity, inverse, and associativity replay. | Binary operation congruence: equal operands must give equal products. | arbitrary group theorems, Lagrange, Sylow, classification |
| `finite-monoids-v0` | Transformation-table composition, units, idempotents, and associativity replay. | A malformed associativity row is isolated as one equality conflict. | arbitrary monoid theory and semigroup structure theorems |
| `finite-permutation-groups-v0` | Finite self-map composition, cycle/sign replay, action replay. | A non-bijection row isolates duplicate-image injectivity failure. | general permutation-group and representation theory |
| `finite-group-actions-v0` | Identity and compatibility laws, orbit/stabilizer replay, Burnside average. | The malformed identity action isolates `e.x = x` for one point. | orbit-stabilizer and Burnside/Cauchy-Frobenius in full generality |
| `finite-algebra-homomorphisms-v0` | Group/ring homomorphism table replay, kernel/image, quotient, induced map. | Preservation congruence and concrete bad-map equality conflicts are checked separately. | first isomorphism theorem, normal subgroup and ideal quotient theory |
| `finite-ideals-v0` | Ideal closure, generated ideal, ring-homomorphism kernel/image, quotient-ring tables. | Bad additive closure and quotient representative congruence become distinct equality artifacts. | general ideal, quotient-ring, and correspondence theorems |
| `finite-vector-spaces-v0` | Finite subspaces, spans, linear maps, kernel/image, rank-nullity replay. | Bad subspace closure is promoted only after replay finds the failing sum. | arbitrary vector-space theorem schemas |
| `finite-dual-spaces-v0` | Finite covector tables, dual basis, annihilator, transpose replay. | Bad covector additivity is checked as a finite function equality conflict. | general dual-space and functorial theorem statements |
| `finite-modules-v0` | Module action, generated submodule, module homomorphism, quotient-module replay. | Bad scalar closure is isolated as a membership/equality conflict. | exact sequences, projective/injective modules, homological algebra |
| `finite-tensor-products-v0` | Tensor basis/dimension, bilinear map, factorization, Kronecker replay. | Bad left-additivity is checked as a finite map equality conflict. | tensor-product universal property and multilinear algebra in general |

## Query It

List the boundary concept:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field abstract_algebra \
  --text "equality certificate" \
  --require-any
```

List packs covered by the boundary:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_algebra_equality_certificate_boundary \
  --route Alethe \
  --require-any
```

Display checked rows under the boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_algebra_equality_certificate_boundary \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Compare with the broader route family:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --kind example-family \
  --text algebra \
  --require-any

python3 scripts/query-foundational-resources.py routes \
  --route Alethe \
  --field abstract_algebra \
  --require-any
```

## Replay It

Replay the finite algebra packs before trusting any certificate:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-groups-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-monoids-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-permutation-groups-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-group-actions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-algebra-homomorphisms-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-ideals-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-vector-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dual-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-modules-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-tensor-products-v0
```

Then check the shared equality-certificate route:

```sh
cargo test -p axeyum-solver --test math_resource_uf_routes
```

## Graduation Criteria

A future algebra row can join this boundary when it has:

1. a finite source object that the pack validator replays directly;
2. a single isolated equality or congruence obligation worth checking
   independently;
3. a committed SMT-LIB source artifact;
4. a `math_resource_uf_routes` regression that emits and rechecks Alethe
   evidence;
5. learner and consumer-query docs that keep replay, certificate checking, and
   theorem horizons separate.

Rows that merely add another table entry should stay replay-only. Rows that
claim general algebraic theorems should stay Lean horizon until they have a
no-`sorry` theorem route.

## Related Pages

- [Algebra And Number Theory](algebra-and-number-theory.md)
- [Finite Algebra Homomorphisms](finite-algebra-homomorphisms-end-to-end.md)
- [Finite Ideals And Quotient Rings](finite-ideals-quotient-rings-end-to-end.md)
- [Finite Modules](finite-modules-end-to-end.md)
- [Finite Tensor Products](finite-tensor-products-end-to-end.md)
- [Alethe Certificate Anatomy](alethe-certificate-anatomy-end-to-end.md)
- [QF_UF / Alethe Congruence Evidence](../../proof-cookbook/recipes/qf-uf-congruence-alethe.md)

## Validation

This page adds a queryable bridge concept and a learner boundary over existing
validated packs. It should increase concept rows by one and leave pack/check
counts unchanged.

```sh
./scripts/check-foundational-resources.sh
./scripts/check-links.sh
```
