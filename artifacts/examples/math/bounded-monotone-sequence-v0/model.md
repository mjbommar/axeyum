# Model

The pack uses the rational sequence:

```text
a_n = n / (n + 1)
```

The finite prefix row lists indices `0..6`:

```text
0, 1/2, 2/3, 3/4, 4/5, 5/6, 6/7
```

The validator checks each value exactly, then checks:

```text
a_0 < a_1 < ... < a_6
a_i < 1 for every listed i
max(prefix) = 6/7 at index 6
```

## Tail Gap

The tail-gap row lists indices `0..8` and checks the finite tail `4..8` against
`epsilon = 1/4` and proposed limit `1`:

```text
1 - a_4 = 1/5
1 - a_5 = 1/6
1 - a_6 = 1/7
1 - a_7 = 1/8
1 - a_8 = 1/9
```

The maximum listed tail gap is `1/5`, which is below `1/4`.

## Bad Upper Bound

The malformed source row claims the finite prefix is bounded above by `5/6`.
Exact replay computes:

```text
a_6 = 6/7
```

The separate `qf-lra-bad-upper-bound` row owns the QF_LRA artifact that checks
only the final conflict:

```text
6/7 <= 5/6
```

## Bad Tail Gap

The malformed source row claims the finite tail starting at `n = 2` is already
within `epsilon = 1/4` of the proposed limit `1`. Exact replay computes:

```text
a_2 = 2/3
1 - a_2 = 1/3
1/3 - 1/4 = 1/12
```

The separate `qf-lra-bad-tail-gap` row owns the QF_LRA artifact that checks
only the final conflict:

```text
tail_excess = 1/12
tail_excess <= 0
```

These rows are finite exact-rational replay targets. They are not a proof that
every bounded monotone sequence converges.
