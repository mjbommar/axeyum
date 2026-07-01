# Model

Each witness describes a one-dimensional affine recurrence over exact rationals:

```text
x(t+1) = x(t) + delta
```

The finite horizon is explicit. A trace with `steps = n` must contain exactly
`n + 1` states, including the initial state.

## Trace Witness

For `initial = 0`, `delta = 2`, and `steps = 4`, the trace is:

```text
0, 2, 4, 6, 8
```

## Bad Transition Step

The same trace supplies a checked negative transition row. Exact replay
computes:

```text
2 + 2 = 4
```

so the malformed claim that the next state is `5` is rejected by the
source-linked QF_LRA/Farkas artifact.

## Invariant Witness

The same trace is checked against the closed interval:

```text
0 <= x(t) <= 8
```

for every listed state.

## Bad Invariant Bound

The same trace also supplies a checked negative row. Exact replay computes:

```text
max(0, 2, 4, 6, 8) = 8
```

so the malformed invariant upper bound `x(t) <= 6` is rejected by the
source-linked QF_LRA/Farkas artifact.

## Reachability Witness

For `initial = 0`, `delta = 3`, and `steps = 3`, the trace is:

```text
0, 3, 6, 9
```

The threshold `x(t) >= 7` is false at steps `0`, `1`, and `2`, and true at
step `3`.

These are bounded replay targets. They are not general statements about
continuous dynamics, numerical convergence, or asymptotic behavior.
