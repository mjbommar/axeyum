# Checks

## `pmf-total-mass`

Expected result: `sat`.

The witness is a fair six-sided die probability mass function. The validator
checks each mass is in `[0, 1]` and the total is exactly `1`.

## `conditional-probability-witness`

Expected result: `sat`.

The witness is a four-atom joint table for `rain` and `late`. The validator
recomputes `P(late | rain)` from atom masses and checks it is exactly `1/3`.

## `bayes-posterior-witness`

Expected result: `sat`.

The witness gives a prior, sensitivity, false-positive rate, and posterior.
The validator recomputes Bayes rule exactly and checks the posterior is `2/13`.
