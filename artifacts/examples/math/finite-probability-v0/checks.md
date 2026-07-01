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

## `bad-conditional-probability-rejected`

Expected result: `unsat`.

The row fixes the same four-atom rain/late table but claims
`P(late | rain) = 1/2`. The validator recomputes `P(rain) = 3/10` and
`P(late and rain) = 1/10`, so the exact conditional probability is `1/3`.

The resource-backed Axeyum regression checks the division-free linear equation
as `QF_LRA`: `P(rain) * p = P(late and rain)` and `p = 1/2`, requiring
rechecked `UnsatFarkas` evidence.

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

## `independence-witness`

Expected result: `sat`.

The witness is a four-atom table for a coin event and a color event. The
validator recomputes `P(heads)=1/2`, `P(red)=1/2`, and
`P(heads and red)=1/4`, then checks the finite independence equation.

Proof route: finite-model replay today. Impossible independence claims belong
on the QF_LRA/Farkas route once the finite marginals have been replayed.

## `bad-independence-rejected`

Expected result: `unsat`.

The row fixes the same four-atom table but claims `P(heads and red)=1/3` while
retaining the independence equation with marginals `1/2` and `1/2`. Exact
replay computes the required product as `1/4`.

The resource-backed Axeyum regression checks the final linear contradiction as
`QF_LRA`: `joint_probability = independence_product`,
`independence_product = 1/4`, and `joint_probability = 1/3`, requiring
rechecked `UnsatFarkas` evidence.

## `total-variation-witness`

Expected result: `sat`.

The witness compares two normalized three-atom distributions. The validator
recomputes the absolute atomwise differences as `1/6`, `0`, and `1/6`, sums the
`l1` distance as `1/3`, and checks total variation as `1/6`.

Proof route: finite-model replay today. Impossible finite distribution-distance
claims belong on the QF_LRA/Farkas route after the absolute-difference table has
been replayed exactly.

## `bad-total-variation-rejected`

Expected result: `unsat`.

The row fixes the same two finite distributions but claims total variation
distance `1/4`. Exact replay computes `l1_distance = 1/3`, so the true total
variation distance is `1/6`.

The resource-backed Axeyum regression checks the final linear contradiction as
`QF_LRA`: `2 * total_variation = l1_distance`, `l1_distance = 1/3`, and
`total_variation = 1/4`, requiring rechecked `UnsatFarkas` evidence.
