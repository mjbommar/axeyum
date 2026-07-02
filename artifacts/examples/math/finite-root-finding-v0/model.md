# Model

The pack uses exact rational arithmetic for the polynomial:

```text
f(x) = x^2 - 2
f'(x) = 2*x
```

## Bisection Step

```text
left = 1
right = 2
midpoint = 3/2
f(left) = -1
f(midpoint) = 1/4
f(right) = 2
```

The sign change is between `1` and `3/2`, and the interval width drops from
`1` to `1/2`.

## Newton Step

```text
current = 3/2
f(current) = 1/4
f'(current) = 3
next = current - f(current) / f'(current) = 17/12
f(next) = 1/144
```

The residual decreases in this fixed row:

```text
1/144 < 1/4
```

## Bad Newton Row

The bad source row keeps the exact replay result `17/12` fixed and claims the
same Newton iterate is `4/3`. Exact replay rejects that source claim. The
separate `qf-lra-bad-newton-step` row records the final equality conflict as a
tiny linear contradiction.

## Bad Bisection Width Row

The selected interval from the bisection replay is:

```text
[1, 3/2]
```

Its exact width is `1/2`. The bad source row claims width `1/3`, leaving
positive width excess `1/6`; the separate `qf-lra-bad-bisection-width` row
checks that this positive excess cannot also be nonpositive.
