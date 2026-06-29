# Checks

## `pmf-total-mass`

Expected result: `sat`.

The witness is a fair six-sided die probability mass function. The validator
checks each mass is in `[0, 1]` and the total is exactly `1`.

Proof route: finite-model replay today. A future invalid normalization or
nonnegativity claim should emit a QF_LRA/Farkas certificate.

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

Proof route: finite-model replay today. A future impossible Bayes-rule
constraint should emit a QF_LRA/Farkas certificate.
