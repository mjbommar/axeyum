# Model

All values are exact rational values. The pack checks finite prefixes and
finite tails only.

The reciprocal-tail row uses:

```text
a_n = 1 / (n + 1)
limit = 0
epsilon = 1/3
start_index = 3
horizon = 8
```

The validator checks every listed value and every index from `3` through `8`.

The constant-sequence counterexample row records that `a_5 = 1` is not within
`1/2` of the proposed limit `0`.

The monotone-prefix row checks a finite prefix of:

```text
a_n = n / (n + 1)
```

The geometric row checks a fixed partial sum:

```text
sum_{k=0}^4 (1/2)^k = (1 - (1/2)^5) / (1 - 1/2) = 31/16
```

The Cauchy-tail row is a bounded no-counterexample check over a listed finite
tail. It does not prove the sequence is Cauchy.

For the promoted Cauchy-tail row, finite replay computes the largest pairwise
distance in `[1/3, 1/4, 1/5, 1/6, 1/7]` as `1/3 - 1/7 = 4/21`. The source
SMT-LIB artifact then asks Axeyum to refute the contradictory threshold claim
`max_pair_distance >= 1/2` with QF_LRA/Farkas evidence.
