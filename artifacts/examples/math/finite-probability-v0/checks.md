# Checks

## `pmf-total-mass`

Expected result: `sat`.

The witness is a fair six-sided die probability mass function. The validator
checks each mass is in `[0, 1]` and the total is exactly `1`.

Proof route: finite-model replay today. A future invalid normalization or
nonnegativity claim should emit a QF_LRA/Farkas certificate.

## `bad-normalization-rejected`

Expected result: `unsat`.

The row fixes `heads = 1/2`, `tails = 1/2`, and `total = heads + tails`, then
claims `total = 3/2`. The validator recomputes the atom total as `1` and rejects
the false claim.

The resource-backed Axeyum regression checks the final linear obligation as
`QF_LRA`, requiring rechecked `UnsatFarkas` evidence.

## `conditional-probability-witness`

Expected result: `sat`.

The witness is a four-atom joint table for `rain` and `late`. The validator
recomputes `P(late | rain)` from atom masses and checks it is exactly `1/3`.

Proof route: finite-model replay today. A future inconsistent conditional
probability claim should emit a QF_LRA/Farkas certificate.

## `bayes-posterior-witness`

Expected result: `sat`.

The witness gives a prior, sensitivity, false-positive rate, and posterior.
The validator recomputes Bayes rule exactly and checks the posterior is `2/13`.

Proof route: finite-model replay today. Impossible Bayes-rule constraints
belong on the QF_LRA/Farkas route.

## `bad-bayes-posterior-rejected`

Expected result: `unsat`.

The row fixes the same diagnostic-test parameters but claims posterior
`P(disease | positive) = 1/5`. The validator recomputes the evidence
probability as `117/2000` and the disease-positive probability as `9/1000`.

The resource-backed Axeyum regression checks the final linear Bayes equation as
`QF_LRA`: `evidence_probability * posterior = disease_and_positive_probability`
and `posterior = 1/5`, requiring rechecked `UnsatFarkas` evidence.
