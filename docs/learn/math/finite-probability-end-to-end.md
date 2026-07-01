# End To End: Conditional Probability, Random Variables, Kernels, Concentration, Martingales, And Product Measures

This lesson follows finite probability resources from atom tables to replayed
conditional probability, finite random variables, conditional expectation,
finite stochastic kernels, finite concentration checks, finite martingales,
exact product measures, and finite expectations. It uses the
[finite-probability-v0](../../../artifacts/examples/math/finite-probability-v0/),
[finite-random-variables-v0](../../../artifacts/examples/math/finite-random-variables-v0/),
[finite-conditional-expectation-v0](../../../artifacts/examples/math/finite-conditional-expectation-v0/),
[finite-stochastic-kernels-v0](../../../artifacts/examples/math/finite-stochastic-kernels-v0/),
[finite-concentration-v0](../../../artifacts/examples/math/finite-concentration-v0/),
[finite-martingales-v0](../../../artifacts/examples/math/finite-martingales-v0/),
[finite-product-measure-v0](../../../artifacts/examples/math/finite-product-measure-v0/),
and [finite-integration-v0](../../../artifacts/examples/math/finite-integration-v0/)
packs.
For the single-pack first-principles finite probability table view, read
[End To End: Finite Probability Mass Tables](finite-probability-mass-tables-end-to-end.md).

Concept rows:

- `field_probability_theory`, `field_statistics`, and `field_measure_theory` in
  the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_counting` and `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `pmf-total-mass` | `sat` | replay-only |
| `bad-normalization-rejected` | `unsat` | checked |
| `conditional-probability-witness` | `sat` | replay-only |
| `bad-conditional-probability-rejected` | `unsat` | checked |
| `bayes-posterior-witness` | `sat` | replay-only |
| `bad-bayes-posterior-rejected` | `unsat` | checked |
| `pushforward-distribution-witness` | `sat` | replay-only |
| `expectation-through-pushforward-witness` | `sat` | replay-only |
| `independent-random-variables-witness` | `sat` | replay-only |
| `bad-pushforward-rejected` | `unsat` | checked |
| `bad-expectation-through-pushforward-rejected` | `unsat` | checked |
| `conditional-expectation-partition-witness` | `sat` | replay-only |
| `law-total-expectation-witness` | `sat` | replay-only |
| `tower-property-witness` | `sat` | replay-only |
| `bad-conditional-expectation-rejected` | `unsat` | checked |
| `bad-tower-property-rejected` | `unsat` | checked |
| `kernel-normalization-witness` | `sat` | replay-only |
| `kernel-pushforward-witness` | `sat` | replay-only |
| `joint-disintegration-witness` | `sat` | replay-only |
| `kernel-composition-witness` | `sat` | replay-only |
| `bad-kernel-row-rejected` | `unsat` | checked |
| `markov-inequality-witness` | `sat` | replay-only |
| `chebyshev-inequality-witness` | `sat` | replay-only |
| `union-bound-witness` | `sat` | replay-only |
| `bad-concentration-bound-rejected` | `unsat` | checked |
| `finite-martingale-witness` | `sat` | replay-only |
| `square-submartingale-witness` | `sat` | replay-only |
| `bounded-stopping-replay` | `sat` | replay-only |
| `bad-stopped-expectation-rejected` | `unsat` | checked |
| `bad-martingale-rejected` | `unsat` | checked |
| `product-measure-table-witness` | `sat` | replay-only |
| `marginalization-witness` | `sat` | replay-only |
| `finite-fubini-witness` | `sat` | replay-only |
| `bad-product-measure-rejected` | `unsat` | checked |
| `bad-product-marginal-rejected` | `unsat` | checked |
| `simple-function-integral-witness` | `sat` | replay-only |
| `bad-expectation-rejected` | `unsat` | checked |

Every check is exact finite replay over rational numbers.

## Encode

The conditional-probability witness is a four-atom joint table:

```text
rain_late    = 1/10
rain_on_time = 1/5
dry_late     = 1/5
dry_on_time  = 1/2
```

The claimed query is:

```text
P(late | rain) = 1/3
```

The bad normalization row is a direct exact-rational contradiction:

```text
P(heads) = 1/2
P(tails) = 1/2
total = P(heads) + P(tails)
total = 3/2
```

The bad conditional-probability row keeps the same rain/late table but claims:

```text
P(late | rain) = 1/2
```

Exact replay computes `P(rain)=3/10` and `P(late and rain)=1/10`; the checked
linear contradiction is the division-free equation:

```text
P(rain) * p = P(late and rain)
p = 1/2
```

The Bayes posterior witness uses:

```text
P(disease) = 1/100
P(positive | disease) = 9/10
P(positive | not disease) = 1/20
P(disease | positive) = 2/13
```

The bad Bayes row keeps the same diagnostic-test parameters but claims
posterior `1/5`. Exact replay computes:

```text
disease_and_positive_probability = 9/1000
evidence_probability = 117/2000
```

The checked `QF_LRA` contradiction is:

```text
evidence_probability * posterior = disease_and_positive_probability
posterior = 1/5
```

The finite integration witness is a three-atom table:

```text
P(low) = 1/4
P(mid) = 1/4
P(high) = 1/2
f(low), f(mid), f(high) = 0, 2, 4
```

The product-measure witness crosses a fair coin with a fair three-sided die:

```text
P(heads) = P(tails) = 1/2
Q(one) = Q(two) = Q(three) = 1/3
R(x,y) = P(x) * Q(y)
```

The random-variable witness maps weather atoms to commute-time outcomes:

```text
P(clear) = 1/2
P(rain) = P(storm) = 1/4
X(clear), X(rain), X(storm) = short, medium, long
```

The conditional-expectation witness uses a finite partition:

```text
P(a) = P(b) = P(c) = P(d) = 1/4
X(a), X(b), X(c), X(d) = 0, 2, 4, 8
G = {a,b}, {c,d}
```

The stochastic-kernel witness maps weather states to commute choices:

```text
K(sunny, walk) = 3/4
K(sunny, bus) = 1/4
K(rainy, walk) = 1/5
K(rainy, bus) = 4/5
mu(sunny), mu(rainy) = 2/3, 1/3
```

The martingale witness uses a two-step fair walk and its natural filtration:

```text
atoms = uu, ud, du, dd
F0 = {uu, ud, du, dd}
F1 = {uu, ud}, {du, dd}
F2 = {uu}, {ud}, {du}, {dd}
M0 = 0
M1 = 1 on {uu,ud}, -1 on {du,dd}
M2(uu), M2(ud), M2(du), M2(dd) = 2, 0, 0, -2
```

The finite concentration witness uses a two-point nonnegative random variable:

```text
P(low) = 3/4
P(high) = 1/4
X(low) = 0
X(high) = 4
```

## Replay

The checker recomputes:

```text
P(rain) = 1/10 + 1/5 = 3/10
P(late and rain) = 1/10
P(late | rain) = (1/10) / (3/10) = 1/3
```

It also checks that the table is normalized and that every atom probability is
in `[0,1]`.

For the bad normalization row, the validator recomputes `1/2 + 1/2 = 1`. The
solver regression checks the same final obligation as `QF_LRA` and requires
`Evidence::UnsatFarkas` to pass `Evidence::check`.

For the integration row, the checker recomputes:

```text
integral f dP = 0*(1/4) + 2*(1/4) + 4*(1/2) = 5/2
```

It also checks an indicator integral, finite linearity, and rejects the false
claim `integral f dP = 3`.
For a fuller focused trace, read
[End To End: Finite Integration](finite-integration-end-to-end.md).

For the random-variable row, the checker recomputes:

```text
P(X = short) = 1/2
P(X = medium) = 1/4
P(X = long) = 1/4
E[X] = 10*(1/2) + 20*(1/4) + 40*(1/4) = 20
```

It also checks a four-atom independence witness by recomputing the joint table
and comparing each joint mass to the product of its marginals. It now also
rejects the false expectation claim `E[X] = 25` with checked `UnsatFarkas`
evidence after replay computes `E[X] = 20`.

For a fuller focused trace, read
[End To End: Finite Random Variables](finite-random-variables-end-to-end.md).

For the conditional-expectation row, the checker recomputes:

```text
E[X | {a,b}] = (0*(1/4) + 2*(1/4)) / (1/2) = 1
E[X | {c,d}] = (4*(1/4) + 8*(1/4)) / (1/2) = 6
E[E[X | G]] = E[X] = 7/2
```

It also checks a finite tower-property row for a two-block partition refining
the one-block partition, and rejects a false tower value with checked
QF_LRA/Farkas evidence.

For a fuller focused trace, read
[End To End: Finite Conditional Expectation](finite-conditional-expectation-end-to-end.md).

For the finite stochastic-kernel row, the checker recomputes:

```text
nu(walk) = 2/3*3/4 + 1/3*1/5 = 17/30
nu(bus) = 2/3*1/4 + 1/3*4/5 = 13/30
P(sunny, walk) = mu(sunny) * K(sunny, walk) = 1/2
K(sunny, walk) = P(sunny, walk) / mu(sunny) = 3/4
```

It also checks row normalization, target marginals, recovery of kernel rows
from a finite joint table, kernel composition, and a malformed row that sums to
`6/5`.

For a fuller focused trace, read
[End To End: Finite Stochastic Kernels](finite-stochastic-kernels-end-to-end.md).

For concentration, the checker recomputes:

```text
E[X] = 1
P(X >= 2) = 1/4
E[X] / 2 = 1/2
```

It also checks a finite Chebyshev row, a finite union-bound row, and rejects the
false claim `P(X >= 2) <= 1/8`.

For a fuller focused trace, read
[End To End: Finite Concentration](finite-concentration-end-to-end.md).

For the finite martingale row, the checker recomputes:

```text
E[M1 | F0] = 0 = M0
E(M2 | F1, {uu,ud}) = 1 = M1 on {uu,ud}
E(M2 | F1, {du,dd}) = -1 = M1 on {du,dd}
```

It also checks that `M_t` is adapted to `F_t`, that `M_t^2` is a finite
submartingale, and that the bounded stopping time `tau = first hit +1 capped at
2` satisfies `E[M_tau] = E[M0] = 0` by exact rational summation. The bad
stopped-expectation row keeps that finite replay but rejects the false claim
`E[M_tau] = 1/2` through checked Farkas evidence.

For a fuller focused trace, read
[End To End: Finite Martingales](finite-martingales-end-to-end.md).

For the product-measure row, the checker recomputes:

```text
R(heads, one) = (1/2) * (1/3) = 1/6
R({heads} x {two, three}) = 1/3
sum_y R(heads, y) = 1/2
sum_x R(x, two) = 1/3
```

The checked bad marginal row rejects the malformed claim
`sum_y R(heads, y) = 2/3` after replay computes the row sum as `1/2`.

For the finite Fubini row, it checks the direct finite sum and both iterated
sums over the same product table:

```text
sum_(x,y) f(x,y) R(x,y) = 3
sum_x P(x) * sum_y f(x,y) Q(y) = 3
sum_y Q(y) * sum_x f(x,y) P(x) = 3
```

For a fuller focused trace, read
[End To End: Finite Product Measure](finite-product-measure-end-to-end.md).

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-random-variables-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-conditional-expectation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-stochastic-kernels-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-concentration-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-martingales-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-product-measure-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_product_measure_bad_marginal_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-integration-v0
```

Expected output for each command:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The search side may propose a probability table or posterior. The trusted side
only recomputes finite sums, exact rational divisions, and small Farkas
certificates for linear probability refutations. Continuous
probability, general product measures, Fubini/Tonelli, Lebesgue integration,
conditional expectation, regular conditional probabilities, disintegration
theorems, general Markov kernels, general concentration inequalities,
Chernoff/Hoeffding bounds, laws of large numbers, central limit theorems,
general martingale convergence, optional stopping, Doob inequalities,
convergence theorems, and statistical inference are outside this proof claim.
