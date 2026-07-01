# Number And Arithmetic Resource Consumer Queries

This guide turns the number-theory and arithmetic-boundary rows in the
foundational-resource JSON contract into copyable downstream queries. It is a
consumer-discovery layer, not a new proof route and not a claim of broad
number-theory theorem coverage.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked arithmetic packs match this finite number-system family and proof route?
```

The current arithmetic surface is finite and route-explicit: integer linear
obstructions, gcd/Bezout witnesses, CRT and nonunit inverse rows, fixed-width
residue and finite-field QF_BV rows, quotient/ideal equality rows, totality
convention rows, and exact-vs-floating boundary rows. Analytic number theory,
algebraic number theory, unbounded induction, prime distribution, general
field/ring theory, floating-point roundoff guarantees, and asymptotic
algorithmic number theory remain in the proof-horizon or numerical-honesty
lanes.

## Query Shape

Start with number-theory summaries by route:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field number_theory \
  --route Diophantine \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field number_theory \
  --route qf-bv \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field number_theory \
  --route Alethe \
  --require-any
```

Then drill into the bridge concepts that downstream consumers usually mean by
"arithmetic":

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_gcd_divisibility_witness \
  --route Diophantine \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_gcd_divisibility_witness \
  --route Diophantine \
  --proof-status checked \
  --require-any
```

Use `packs` for catalog cards and pack paths. Use `checks` when the consumer
needs concrete checked rows to display.

## Arithmetic Query Families

| Arithmetic Family | Concept Filter | Route Filter | Start Query |
|---|---|---|---|
| GCD, Bezout, and divisibility obstructions | `bridge_gcd_divisibility_witness` | `Diophantine` | `checks --concept bridge_gcd_divisibility_witness --route Diophantine --proof-status checked` |
| CRT and nonunit inverse arithmetic | `bridge_modular_crt_inverse_witness` | `Diophantine`; `qf-bv` | `checks --concept bridge_modular_crt_inverse_witness --route Diophantine --proof-status checked`; `checks --concept bridge_modular_crt_inverse_witness --route qf-bv --proof-status checked` |
| Fixed-width residue and finite-field certificates | `bridge_qf_bv_bitblast_anatomy` | `qf-bv` | `checks --concept bridge_qf_bv_bitblast_anatomy --route qf-bv --proof-status checked` |
| Totality and operation-convention rows | `bridge_totality_conventions` | any route | `checks --concept bridge_totality_conventions --proof-status checked` |
| Quotient and ideal arithmetic rows | `bridge_ideal_closure` | `Alethe` | `checks --concept bridge_ideal_closure --route Alethe --proof-status checked` |
| Exact rational versus floating boundary rows | `bridge_exact_vs_floating_arithmetic` | `Farkas` | `checks --concept bridge_exact_vs_floating_arithmetic --route Farkas --proof-status checked` |

## Copyable Examples

Display checked Diophantine arithmetic rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field number_theory \
  --route Diophantine \
  --proof-status checked \
  --require-any
```

Display checked fixed-width QF_BV arithmetic rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field number_theory \
  --route qf-bv \
  --proof-status checked \
  --require-any
```

Display gcd and divisibility rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_gcd_divisibility_witness \
  --route Diophantine \
  --proof-status checked \
  --require-any
```

Display modular CRT and inverse rows by proof route:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_modular_crt_inverse_witness \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_modular_crt_inverse_witness \
  --route qf-bv \
  --proof-status checked \
  --require-any
```

Display totality-convention rows across arithmetic packs:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_totality_conventions \
  --proof-status checked \
  --require-any
```

Display exact-vs-floating boundary rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_exact_vs_floating_arithmetic \
  --route Farkas \
  --proof-status checked \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked arithmetic rows, not
theorem coverage. They can support a catalog, learner page, solver-regression
search, or sibling resource that needs examples by arithmetic object family.

They do not prove:

- analytic or algebraic number theory;
- unbounded induction or general Peano arithmetic theorem schemas;
- prime distribution, primality algorithm, or factorization-complexity claims;
- arbitrary ring/field/module structure theorems;
- floating-point roundoff, conditioning, or numerical-stability guarantees;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction,
numeric-honesty artifacts, or benchmark evidence before they can graduate.
