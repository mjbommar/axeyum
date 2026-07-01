# Checks

## `binomial-tail-pvalue`

Expected result: `sat`.

The validator recomputes the exact finite binomial right-tail sum for
`n = 4`, `k = 3`, and `p0 = 1/2`.

## `hypergeometric-point-probability`

Expected result: `sat`.

The validator recomputes the fixed-margin hypergeometric point probability for
the listed `2x2` table.

## `fisher-left-tail-pvalue`

Expected result: `sat`.

The validator sums the exact fixed-margin hypergeometric probabilities for all
top-left counts at or below the observed top-left count.

## `fisher-two-sided-pvalue`

Expected result: `sat`.

The validator uses the explicit probability-ordered two-sided convention: it
sums every fixed-margin table whose hypergeometric point probability is no
larger than the observed table probability. For this table, those are top-left
counts `0`, `1`, `3`, and `4`.

## `multinomial-probability-ordered-pvalue`

Expected result: `sat`.

The validator enumerates every three-category count vector summing to `3`
under uniform category probabilities. With observed counts `[3,0,0]`, the
observed point probability is `1/27`, so the probability-ordered convention
includes exactly `[3,0,0]`, `[0,3,0]`, and `[0,0,3]`, for p-value `1/9`.

## `bad-fisher-left-tail-rejected`

Expected result: `unsat`.

The validator recomputes the fixed-margin Fisher left tail as
`(1 + 16) / 70 = 17/70`. The source artifact asks QF_LRA to reject the final
linear conflict:

```text
70 * fisher_left_tail_p_value = 17
fisher_left_tail_p_value = 1/4
```

Proof route: checked QF_LRA/Farkas evidence. The finite hypergeometric count
sum remains replayed by the pack validator.

## `bad-fisher-two-sided-rejected`

Expected result: `unsat`.

The validator recomputes the probability-ordered two-sided Fisher p-value as
`(1 + 16 + 16 + 1) / 70 = 17/35`. The source artifact asks QF_LRA to reject the
final linear conflict:

```text
35 * fisher_two_sided_p_value = 17
fisher_two_sided_p_value = 1/2
```

Proof route: checked QF_LRA/Farkas evidence. The finite hypergeometric count
sum and the two-sided convention remain replayed by the pack validator.

## `bad-multinomial-pvalue-rejected`

Expected result: `unsat`.

The validator recomputes the exact probability-ordered multinomial p-value as
`3 * (1/27) = 1/9`. The source artifact asks QF_LRA to reject the final linear
conflict:

```text
9 * multinomial_p_value = 1
multinomial_p_value = 1/6
```

Proof route: checked QF_LRA/Farkas evidence. The finite multinomial
enumeration and probability-order convention remain replayed by the pack
validator.

## `bad-binomial-pvalue-rejected`

Expected result: `unsat`.

The exact right-tail p-value is `5/16`, so the claimed value `1/4` is false.
This is a checked finite arithmetic rejection, not an emitted proof object yet.

## `qf-lia-bad-binomial-tail-count`

Expected result: `unsat`.

The SMT-LIB artifact encodes the rejected binomial p-value numerator as an
integer count contradiction: `C(4,3) = 4`, `C(4,4) = 1`, `tail_count = 4 + 1`,
and the false claim `tail_count = 4`. Axeyum emits and checks an
`UnsatDiophantine` certificate for those inconsistent equalities.
