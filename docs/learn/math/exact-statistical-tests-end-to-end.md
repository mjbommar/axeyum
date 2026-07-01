# End To End: Exact Statistical Tests

This lesson follows one finite statistics resource from count data to exact
p-value replay. It uses
[exact-statistical-tests-v0](../../../artifacts/examples/math/exact-statistical-tests-v0/).

Concept rows:

- `curriculum_counting`, `curriculum_rationals`, and `curriculum_naturals` in
  the [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_statistics`, `field_probability_theory`, and `field_discrete_math` in
  the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `binomial-tail-pvalue` | `sat` | replay-only |
| `hypergeometric-point-probability` | `sat` | replay-only |
| `fisher-left-tail-pvalue` | `sat` | replay-only |
| `bad-fisher-left-tail-rejected` | `unsat` | checked |
| `bad-binomial-pvalue-rejected` | `unsat` | checked |
| `qf-lia-bad-binomial-tail-count` | `unsat` | checked |

Every row is exact finite arithmetic over integer counts and rational
probabilities. The pack does not claim asymptotic tests, normal
approximations, calibration guarantees, floating-point library behavior, or
model-selection validity.

## Replay A Binomial Tail

The binomial witness fixes:

```text
n = 4
observed successes = 3
p0 = 1/2
tail = greater_equal
claimed p-value = 5/16
```

The validator recomputes the right-tail probability exactly:

```text
P(X >= 3) = P(X = 3) + P(X = 4)
          = C(4,3)*(1/2)^3*(1/2)^1 + C(4,4)*(1/2)^4
          = 4/16 + 1/16
          = 5/16
```

No floating point is involved. The p-value is a rational finite sum.

## Replay A Hypergeometric Point Probability

The fixed `2x2` table is:

```text
[[1, 3],
 [3, 1]]
```

with row sums:

```text
4, 4
```

and column sums:

```text
4, 4
```

For top-left count `1`, the exact fixed-margin probability is:

```text
C(4,1) * C(4,3) / C(8,4) = 16/70 = 8/35
```

The validator recomputes the row sums, column sums, total count, binomial
coefficients, and rational quotient.

## Replay A One-Sided Fisher Tail

For the same fixed margins, the left-tail top-left counts are `0` and `1`.
The validator sums their hypergeometric probabilities:

```text
P(X = 0) = C(4,0) * C(4,4) / C(8,4) = 1/70
P(X = 1) = C(4,1) * C(4,3) / C(8,4) = 16/70
P(X <= 1) = 17/70
```

This is a finite Fisher exact-test replay for one fixed table. It does not
claim a full statistical testing library.

## Check The Fisher P-Value Certificate

The checked Fisher row keeps the finite counting step outside the solver:

```text
actual left-tail p-value = 17/70
```

Then it asks QF_LRA to reject only the final exact-rational contradiction:

```text
70 * fisher_left_tail_p_value = 17
fisher_left_tail_p_value = 1/4
```

Axeyum derives a Farkas certificate for that inconsistent linear real system
and checks the certificate independently. This is the trusted-small-checking
pattern for exact rational p-values: finite replay computes the rational, and
the solver proof route checks the malformed equality.

## Reject A Bad Binomial P-Value

The checked negative row uses the same binomial setting:

```text
n = 4
observed successes = 3
p0 = 1/2
claimed p-value = 1/4
```

The checker recomputes:

```text
actual p-value = 5/16
```

and rejects the false claim because:

```text
1/4 != 5/16
```

This is the important trust pattern for statistical resources: the search side
may propose a p-value, but the trusted side recomputes it from finite counts.

## Check The Tail Count Certificate

The solver-form row strips the same rejected p-value down to integer counts:

```text
C(4,3) = 4
C(4,4) = 1
tail_count = 4 + 1 = 5
```

A claimed p-value of `1/4` over denominator `16` would require:

```text
tail_count = 4
```

The SMT-LIB artifact asserts both facts as integer equalities:

```text
c3 = 4
c4 = 1
tail_count = c3 + c4
tail_count = 4
```

Axeyum derives an `UnsatDiophantine` certificate for the inconsistent linear
integer system and checks that certificate independently. This upgrades the
bad binomial p-value row from finite replay to a concrete QF_LIA proof-object
route for the count contradiction.

## Name The Horizon

The pack intentionally covers exact finite tests only:

```text
binomial finite tails
hypergeometric point probabilities
one-sided Fisher tails
bad p-value refutations
QF_LRA Fisher p-value contradictions
QF_LIA tail-count contradictions
```

The following remain outside this proof claim:

```text
two-sided Fisher conventions
exact multinomial tests
asymptotic chi-square and z tests
normal approximations
multiple-testing correction policy
floating-point statistical libraries
calibration and model selection
```

Those need additional exact-test packs, numerical-honesty metadata, or
proof-assistant resources before they can be promoted.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/exact-statistical-tests-v0
cargo test -p axeyum-solver --test math_resource_lra_routes exact_stats_bad_fisher_left_tail_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lia_routes exact_stats_bad_binomial_tail_count_emits_checked_diophantine_evidence
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current exact-statistics resource pattern:

```text
untrusted fast search -> p-value or table claim
trusted small checking -> exact finite counts, rational sums, Farkas certificates, and Diophantine certificates
remaining horizon -> asymptotics, policy choices, and floating-point statistics
```

The graduation target is to encode these claims as deterministic finite-count
and rational-arithmetic obligations, replay witnesses through Axeyum, and add
two-sided Fisher and exact multinomial tests before claiming broader exact-test
coverage.
