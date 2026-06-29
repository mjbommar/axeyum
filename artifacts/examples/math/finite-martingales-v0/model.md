# Model

The finite probability space is the two-step fair walk:

```text
P(uu) = P(ud) = P(du) = P(dd) = 1/4
```

The filtration is:

```text
F0 = {uu, ud, du, dd}
F1 = {uu, ud}, {du, dd}
F2 = {uu}, {ud}, {du}, {dd}
```

The process is:

```text
M0 = 0
M1(uu) = M1(ud) = 1
M1(du) = M1(dd) = -1
M2(uu) = 2
M2(ud) = 0
M2(du) = 0
M2(dd) = -2
```

The checker recomputes:

```text
E[M1 | F0] = 0 = M0
E[M2 | F1]({uu,ud}) = (2 + 0) / 2 = 1 = M1 on {uu,ud}
E[M2 | F1]({du,dd}) = (0 - 2) / 2 = -1 = M1 on {du,dd}
```

## Square Submartingale

For `M_t^2`, the checker recomputes:

```text
E[M1^2 | F0] = 1 >= M0^2
E[M2^2 | F1]({uu,ud}) = 2 >= 1
E[M2^2 | F1]({du,dd}) = 2 >= 1
```

## Bounded Stopping

The stopping time is first hit of `+1`, capped at time `2`:

```text
tau(uu) = tau(ud) = 1
tau(du) = tau(dd) = 2
M_tau = 1, 1, 0, -2
E[M_tau] = 0 = M0
```

## Bad Martingale Claim

The false claim changes `M2(uu)` from `2` to `3`. The checker rejects it
because `E[M2 | F1]` on the up block becomes `3/2`, not `1`.
