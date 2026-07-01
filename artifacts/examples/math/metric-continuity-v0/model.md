# Model

All distances and function values are exact rationals written as strings
accepted by Python's `Fraction` type.

The finite domain points represent the rational line sample:

```text
p0 = 0
p1 = 1/4
p2 = 1/2
p3 = 1
```

The metric is absolute distance on those points, and the function is:

```text
f(x) = 2x
```

so the listed output values are:

```text
f(p0) = 0
f(p1) = 1/2
f(p2) = 1
f(p3) = 2
```

## Lipschitz Witness

The validator checks every finite pair:

```text
|f(x) - f(y)| <= 2 * d(x,y)
```

## Epsilon-Delta Witness

At `p0`, with `epsilon = 1` and `delta = 1/2`, the domain ball is:

```text
{p | d(p,p0) < 1/2} = {p0, p1}
```

The output epsilon ball around `f(p0) = 0` is:

```text
{p | |f(p) - 0| < 1} = {p0, p1}
```

The validator checks containment exactly.

## Bad Delta

The claimed `delta = 3/4` is rejected because `p2` is inside the domain ball:

```text
d(p0,p2) = 1/2 < 3/4
```

but it is not inside the output epsilon ball:

```text
|f(p2) - f(p0)| = 1 >= 1
```

The final false output-bound claim is linear:

```text
output_distance = 1
output_distance < 1
```

The pack keeps this contradiction on the checked `UnsatFarkas` route.

## Bad Open-Ball Preimage

The open output ball around `0` with radius `1` contains exactly the points
whose output value is strictly less than `1` away from `0`:

```text
{p | |f(p) - 0| < 1} = {p0, p1}
```

The malformed preimage row claims `p2` is also in that preimage. Exact replay
rejects it:

```text
|f(p2) - 0| = 1
1 < 1 is false
```

The final strict-membership contradiction is again linear:

```text
output_distance = 1
output_distance < 1
```

This is a finite exact refutation, not a proof of any general theorem.
