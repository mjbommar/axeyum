# Model

The finite measure space has three atoms:

```text
P(low) = 1/4
P(mid) = 1/4
P(high) = 1/2
```

The simple function is:

```text
f(low) = 0
f(mid) = 2
f(high) = 4
```

The validator recomputes:

```text
integral f dP = 0*(1/4) + 2*(1/4) + 4*(1/2) = 5/2
```

## Indicator Integral

For the event `{high}`, the checker computes:

```text
P({high}) = 1/2
integral 1_{high} dP = 1/2
```

## Linearity

The second simple function is:

```text
g(low) = 1
g(mid) = 1
g(high) = 3
```

The checker recomputes `integral f = 5/2`, `integral g = 2`, and:

```text
integral (2*f - g) dP = 2*(5/2) - 2 = 3
```

## Bad Expectation Claim

The false claim says `integral f dP = 3`. The checker rejects it because the
exact weighted sum is `5/2`.
