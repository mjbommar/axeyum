# Foundations And Discrete Resource Consumer Queries

This guide turns the logic/proof, set-theory/foundations, and discrete-math
rows in the foundational-resource JSON contract into copyable downstream
queries. It is a consumer-discovery layer, not a new proof route and not a
claim of full proof-assistant, ZFC, or asymptotic combinatorics coverage.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked finite proof, set, counting, or discrete rows match this proof route?
```

The current surface is finite and route-explicit: Boolean truth-table and
CNF/LRAT-style refutation rows, finite countermodel replay, finite
proof-pattern replay, bounded induction obligations, finite
predicate/quantifier expansion, finite set identities, cardinality and
bijection replay, Boolean-algebra rows, finite counting and pigeonhole rows,
partition/equivalence-class roundtrips, and finite relation/function/image/
preimage tables. Full proof automation, ZFC, ordinals, choice, infinite
cardinal arithmetic, unbounded induction, asymptotic enumeration, and broad
combinatorial theorem families remain in the proof-horizon lane.

## Query Shape

Start with field summaries by route:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field logic_and_proof \
  --route boolean \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field set_theory_and_foundations \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field discrete_math \
  --route Diophantine \
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

Use `boolean` for propositional/CNF and finite Boolean-algebra rows, `Alethe`
for equality-heavy relation/function/quotient rows, and `Diophantine` or `LIA`
for finite counting and bounded arithmetic obligations.

## Foundations And Discrete Query Families

| Family | Concept Or Pack Filter | Route Filter | Start Query |
|---|---|---|---|
| Boolean proof, CNF, and LRAT-anatomy rows | `bridge_boolean_cnf_lrat_anatomy` | `boolean` | `checks --concept bridge_boolean_cnf_lrat_anatomy --route boolean --proof-status checked` |
| Refutation-as-query examples | `bridge_refutation_query` | `boolean` | `checks --concept bridge_refutation_query --route boolean --proof-status checked` |
| Finite countermodel replay | `bridge_finite_countermodel_replay` | any checked route | `checks --concept bridge_finite_countermodel_replay --proof-status checked` |
| Finite proof-pattern replay | `bridge_finite_proof_pattern` | any checked route | `checks --concept bridge_finite_proof_pattern --proof-status checked` |
| Bounded induction and arithmetic obligations | `bridge_bounded_induction_obligation` | `LIA` | `checks --concept bridge_bounded_induction_obligation --route LIA --proof-status checked` |
| Finite predicate and quantifier expansion | `bridge_finite_quantifier_expansion` | `Alethe` | `checks --concept bridge_finite_quantifier_expansion --route Alethe --proof-status checked` |
| Finite bijection, cardinality, powerset, and inclusion-exclusion rows | `bridge_finite_bijection_cardinality` | any checked route | `checks --concept bridge_finite_bijection_cardinality --proof-status checked` |
| Finite Boolean algebra rows | `bridge_finite_boolean_algebra` | `boolean` | `checks --concept bridge_finite_boolean_algebra --route boolean --proof-status checked` |
| Finite order and lattice rows | pack `finite-order-lattices-v0` | `Alethe`; `boolean` | `checks --pack finite-order-lattices-v0 --route Alethe --proof-status checked --text antisymmetry`; `checks --pack finite-order-lattices-v0 --route boolean --proof-status checked --text top` |
| Finite counting, pigeonhole, binomial, and generating-function rows | `bridge_finite_counting_replay` | `Diophantine`; `boolean` | `checks --concept bridge_finite_counting_replay --route Diophantine --proof-status checked`; `checks --concept bridge_finite_counting_replay --route boolean --proof-status checked` |
| Partition/equivalence and quotient rows | `bridge_partition_relation_roundtrip` | `Alethe` | `checks --concept bridge_partition_relation_roundtrip --route Alethe --proof-status checked` |
| Finite image/preimage/inverse and function-table rows | `bridge_finite_image_preimage_inverse` | `Alethe` | `checks --concept bridge_finite_image_preimage_inverse --route Alethe --proof-status checked` |

## Copyable Examples

Display checked Boolean proof and CNF rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_boolean_cnf_lrat_anatomy \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_refutation_query \
  --route boolean \
  --proof-status checked \
  --require-any
```

Display finite countermodel rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_countermodel_replay \
  --proof-status checked \
  --require-any
```

Display finite proof-pattern rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_proof_pattern \
  --proof-status checked \
  --require-any
```

Display bounded induction and arithmetic-obligation rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_bounded_induction_obligation \
  --route LIA \
  --proof-status checked \
  --require-any
```

Display finite predicate and quantifier rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_quantifier_expansion \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Display finite cardinality and bijection rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_bijection_cardinality \
  --proof-status checked \
  --require-any
```

Display finite Boolean-algebra rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_boolean_algebra \
  --route boolean \
  --proof-status checked \
  --require-any
```

Display finite counting rows by route:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_counting_replay \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_counting_replay \
  --route boolean \
  --proof-status checked \
  --require-any
```

Display finite partition, relation, function, image, and preimage rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_partition_relation_roundtrip \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_image_preimage_inverse \
  --route Alethe \
  --proof-status checked \
  --require-any
```

For focused UI cards, query individual packs:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack logic-basics-v0 \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack proof-methods-patterns-v0 \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-predicate-v0 \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cardinality-v0 \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack counting-v0 \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack relations-functions-v0 \
  --route Alethe \
  --proof-status checked \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked foundations and discrete
rows, not theorem coverage. They can support a catalog, learner page,
route-specific regression search, or sibling resource that wants examples by
finite proof or finite structure family.

They do not prove:

- full proof automation, general natural-deduction metatheory, or arbitrary
  quantified theorem proving;
- ZFC, ordinals, choice, infinite sets, infinite cardinal arithmetic, or
  complete-lattice theorem schemas;
- unbounded induction or induction over arbitrary predicates;
- asymptotic enumeration, recurrence closed forms, broad combinatorial theorem
  families, or graph-theory theorem coverage beyond the finite graph rows;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction,
benchmark artifacts, or broader solver evidence before they can graduate.
