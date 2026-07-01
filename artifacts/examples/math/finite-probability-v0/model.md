# Model

All probabilities are exact rationals written as strings accepted by Python's
`Fraction` type. A finite probability table is a list of atoms:

```json
{
  "atoms": [
    {"id": "one", "probability": "1/6"},
    {"id": "two", "probability": "1/6"}
  ]
}
```

For conditional probability examples, each atom also carries an `events` list.
The validator computes event probabilities by summing atom probabilities.

## Checks

### Total Mass

The fair die table has six atoms, each with mass `1/6`, so the total mass is
exactly `1`.

The checked bad-normalization row uses the same finite-table shape but asserts a
false total:

```text
P(heads) = 1/2
P(tails) = 1/2
total = P(heads) + P(tails)
total = 3/2
```

The contradiction is linear over exact rationals, so the solver regression
expects an independently rechecked `UnsatFarkas` certificate.

### Conditional Probability

The four-atom rain/late table is:

```text
P(rain and late)     = 1/10
P(rain and on_time)  = 1/5
P(dry and late)      = 1/5
P(dry and on_time)   = 1/2
```

The pack checks:

```text
P(late | rain) = P(late and rain) / P(rain) = (1/10) / (3/10) = 1/3
```

The bad conditional-probability row keeps the same atom table but asserts the
false conditional probability `1/2`. After exact replay computes:

```text
joint_probability = P(late and rain) = 1/10
condition_probability = P(rain) = 3/10
```

the checked linear contradiction is division-free:

```text
condition_probability * conditional_probability = joint_probability
conditional_probability = 1/2
```

### Bayes Posterior

The diagnostic-test table uses:

```text
P(disease) = 1/100
P(positive | disease) = 9/10
P(positive | not disease) = 1/20
```

The pack checks:

```text
P(disease | positive) = 2/13
```

The bad Bayes row keeps the same diagnostic-test parameters but asserts the
false posterior `1/5`. After exact replay computes:

```text
disease_and_positive_probability = 9/1000
evidence_probability = 117/2000
```

the checked linear contradiction is:

```text
evidence_probability * posterior = disease_and_positive_probability
posterior = 1/5
```

These fixed checks are not claims about continuous distributions, sampling, or
statistical inference. They are exact finite-table replay targets.

Certificate route:

- satisfiable finite probability tables remain finite-model replay;
- impossible linear probability constraints, including contradictory
  normalization, nonnegativity, conditioning, or Bayes-rule equations, belong
  on the QF_LRA/Farkas route;
- continuous distributions and sampling claims remain out of proof status.
