# Algebra Structure Consumer Queries

This guide turns the finite algebra rows in the foundational-resource JSON
contract into copyable downstream queries. It is a consumer-discovery layer,
not a new proof route and not a claim about arbitrary algebraic structures.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked algebra packs match this finite structure family and proof route?
```

The current algebra surface is finite and route-explicit: function-table
congruence, finite groups and actions, monoids, homomorphisms, ideals, quotient
representatives, modules, vector spaces, dual spaces, tensor bilinearity, and
fixed-width residue/field rows. Polynomial rows cover fixed coefficient tuples,
division/factor witnesses, finite coefficient windows, and checked root or
discriminant obstructions. General isomorphism theorems, classification
theorems, category-level universal properties, infinite algebra, arbitrary
field/ring/module facts, general factorization, and algebraic closure remain in
the proof-horizon lane.

For the boundary between finite table replay and checked equality certificates,
start with
[Algebra Equality Certificate Boundary](../learn/math/algebra-equality-certificate-boundary.md).

## Query Shape

Start with field summaries:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field abstract_algebra \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field abstract_algebra \
  --route qf-bv \
  --require-any
```

Then drill into bridge concepts or checked rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept <bridge_concept_id> \
  --route <route-substring> \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept <bridge_concept_id> \
  --route <route-substring> \
  --proof-status checked \
  --require-any
```

Use `packs` for a catalog row or pack path. Use `checks` when the consumer
needs concrete checked rows to display.

## Algebra Query Families

| Algebra Family | Concept Filter | Route Filter | Start Query |
|---|---|---|---|
| Algebra equality certificates versus table replay | `bridge_algebra_equality_certificate_boundary` | `Alethe` | `checks --concept bridge_algebra_equality_certificate_boundary --route Alethe --proof-status checked` |
| Group operations, homomorphisms, and permutation rows | `bridge_homomorphism_preservation` | `Alethe` | `checks --concept bridge_homomorphism_preservation --route Alethe --proof-status checked` |
| Group actions and permutation actions | `bridge_group_action` | `Alethe` | `checks --concept bridge_group_action --route Alethe --proof-status checked` |
| Kernels, images, and quotient maps | `bridge_kernel_image`; `bridge_quotient_map` | `Alethe` | `packs --concept bridge_kernel_image --route Alethe`; `packs --concept bridge_quotient_map --route Alethe` |
| Ideals and quotient-ring representatives | `bridge_ideal_closure` | `Alethe` | `checks --concept bridge_ideal_closure --route Alethe --proof-status checked` |
| Modules, vector spaces, dual spaces, and tensor bilinearity | `bridge_module_action`; `bridge_tensor_bilinearity` | `Alethe` | `checks --concept bridge_module_action --route Alethe --proof-status checked`; `packs --concept bridge_tensor_bilinearity --route Alethe` |
| Modular inverses, CRT witnesses, and finite-field nonunits | `bridge_modular_crt_inverse_witness` | `qf-bv` | `checks --concept bridge_modular_crt_inverse_witness --route qf-bv --proof-status checked` |
| GCD, Bezout, divisibility, and integer obstructions | `bridge_gcd_divisibility_witness` | `Diophantine` | `checks --concept bridge_gcd_divisibility_witness --route Diophantine --proof-status checked` |
| Fixed polynomial coefficients, factors, roots, and coefficient windows | `bridge_polynomial_coefficient_factor_replay` | `Diophantine`; `Farkas` | `checks --concept bridge_polynomial_coefficient_factor_replay --route Diophantine --proof-status checked`; `checks --concept bridge_polynomial_coefficient_factor_replay --route Farkas --proof-status checked` |

## Copyable Examples

List equality-heavy algebra packs:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field abstract_algebra \
  --route Alethe \
  --require-any
```

Display checked Alethe algebra rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field abstract_algebra \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Display the algebra equality-certificate boundary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field abstract_algebra \
  --text "equality certificate" \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_algebra_equality_certificate_boundary \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_algebra_equality_certificate_boundary \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Display checked homomorphism and finite-group operation rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_homomorphism_preservation \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Display checked finite group-action rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_group_action \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Display the finite module scalar-closure certificate row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-modules-v0 \
  --route Alethe \
  --proof-status checked \
  --text scalar-closure \
  --require-any
```

Display the finite vector-space additive-closure certificate row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-vector-spaces-v0 \
  --route Alethe \
  --proof-status checked \
  --text addition-closure \
  --require-any
```

List finite ideal and quotient representative packs:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_ideal_closure \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_quotient_map \
  --route Alethe \
  --require-any
```

Display checked module, vector-space, dual-space, and tensor rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_module_action \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-dual-spaces-v0 \
  --route Alethe \
  --proof-status checked \
  --text additivity \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_tensor_bilinearity \
  --route Alethe \
  --require-any
```

Display checked fixed-width finite-field and residue rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_modular_crt_inverse_witness \
  --route qf-bv \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_modular_crt_inverse_witness \
  --route qf-bv \
  --proof-status checked \
  --require-any
```

Display checked integer obstruction rows used by algebra-adjacent number
theory:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_gcd_divisibility_witness \
  --route Diophantine \
  --proof-status checked \
  --require-any
```

Display checked fixed polynomial coefficient, factor, root, and coefficient
window rows:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field abstract_algebra \
  --text polynomial \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_polynomial_coefficient_factor_replay \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_polynomial_coefficient_factor_replay \
  --route Farkas \
  --proof-status checked \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked algebra rows, not
theorem coverage. They can support a catalog, a learner page, a route-specific
regression search, or a sibling resource that wants algebra examples by finite
object family.

They do not prove:

- arbitrary group, ring, field, module, ideal, or tensor theorems;
- isomorphism, structure, classification, Sylow, representation, or
  category-level universal-property theorems;
- infinite algebra or arbitrary-field reasoning;
- quotient, kernel/image, or module theorem schemas beyond the finite replayed
  rows;
- general polynomial factorization, algebraic closure, root distribution, or
  convergence of generating functions;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction, or
benchmark artifacts before they can graduate.
