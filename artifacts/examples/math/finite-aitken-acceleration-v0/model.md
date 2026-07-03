# Model

The checked finite model is Aitken's delta-squared transform:

```text
delta0       = s1 - s0
delta1       = s2 - s1
delta2       = delta1 - delta0
correction   = delta0^2 / delta2
accelerated  = s0 - correction
```

For the geometric-error row:

```text
s0 = 2
s1 = 3/2
s2 = 5/4
delta0 = -1/2
delta1 = -1/4
delta2 = 1/4
correction = (1/4) / (1/4) = 1
accelerated = 2 - 1 = 1
```

For the harmonic-tail row:

```text
s0 = 2
s1 = 3/2
s2 = 4/3
delta0 = -1/2
delta1 = -1/6
delta2 = 1/3
correction = (1/4) / (1/3) = 3/4
accelerated = 2 - 3/4 = 5/4
```

The residual row checks only this finite comparison against the listed target
`1`:

```text
|4/3 - 1| = 1/3
|5/4 - 1| = 1/4
1/4 < 1/3
```

The bad row claims the geometric accelerated value is `3/2`. Exact replay
computes `1`, so the gap is:

```text
3/2 - 1 = 1/2
```
