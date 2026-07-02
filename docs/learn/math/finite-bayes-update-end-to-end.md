# End To End: Finite Bayes Update

This lesson follows the Bayes-update rows inside
[finite-probability-v0](../../../artifacts/examples/math/finite-probability-v0/).
It is a narrow probability-resource page: one diagnostic-test table, one
exact posterior replay, one malformed posterior, and one checked
QF_LRA/Farkas rejection.

Concept rows:

- `field_probability_theory`, `field_statistics`, and `field_measure_theory`
  in the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_probability_mass_table` and `family_exact_rational_farkas` in the
  atlas bridge/example-family vocabulary.

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `bayes-posterior-witness` | `sat` | replay-only |
| `bad-bayes-posterior-rejected` | `unsat` | checked QF_LRA/Farkas |

The row is finite and exact-rational. It checks one diagnostic-test posterior
and rejects one false posterior equation. It does not prove Bayesian
consistency, continuous-density Bayes rules, causal identification,
hierarchical models, posterior convergence, or sampling quality.

## Encode The Diagnostic Test

The resource starts with three exact rational inputs:

```text
P(disease) = 1/100
P(positive | disease) = 9/10
P(positive | not disease) = 1/20
```

The finite table has two hidden states, `disease` and `not disease`, and one
observed event, `positive`. Exact replay computes:

```text
P(disease and positive) = (1/100) * (9/10) = 9/1000
P(not disease and positive) = (99/100) * (1/20) = 99/2000
P(positive) = 9/1000 + 99/2000 = 117/2000
```

Then the posterior is:

```text
P(disease | positive)
  = P(disease and positive) / P(positive)
  = (9/1000) / (117/2000)
  = 18/117
  = 2/13
```

The `bayes-posterior-witness` row is therefore `sat`: the finite data and the
claimed posterior agree under exact rational replay.

## Reject A Bad Posterior

The bad row keeps the same prior, sensitivity, and false-positive rate, but
claims:

```text
posterior = 1/5
```

The checker does not trust that posterior. It recomputes the two source values:

```text
disease_and_positive_probability = 9/1000
evidence_probability = 117/2000
```

The checked `QF_LRA` contradiction is the division-free Bayes equation:

```text
evidence_probability * posterior = disease_and_positive_probability
posterior = 1/5
```

Substituting the malformed posterior gives:

```text
(117/2000) * (1/5) = 117/10000
117/10000 != 9/1000
```

The true posterior satisfies the same equation:

```text
(117/2000) * (2/13) = 9/1000
```

The committed SMT-LIB artifact
[`bad-bayes-posterior-farkas-conflict.smt2`](../../../artifacts/examples/math/finite-probability-v0/smt2/bad-bayes-posterior-farkas-conflict.smt2)
checks the malformed row with rechecked `UnsatFarkas` evidence.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --text Bayes --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --text Bayes --proof-status checked --require-any
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

The first query displays both the replayed posterior row and the checked
malformed-posterior row. The second query filters to the checked
QF_LRA/Farkas rejection.

## Trust Boundary

```text
untrusted fast search -> proposed posterior or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA/Farkas evidence
remaining horizon -> continuous Bayes, posterior convergence, causal inference, MCMC, HMC, VI, and calibration
```

For the wider finite-probability table story, read
[End To End: Finite Probability Mass Tables](finite-probability-mass-tables-end-to-end.md).
