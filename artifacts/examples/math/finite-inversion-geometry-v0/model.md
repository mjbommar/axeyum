# Model

The pack uses inversion in the unit circle centered at the origin:

```text
I(p) = p / |p|^2
```

For `p = (2,1)`:

```text
|p|^2 = 2^2 + 1^2 = 5
I(p) = (2/5, 1/5)
|I(p)|^2 = (2/5)^2 + (1/5)^2 = 1/5
|p|^2 * |I(p)|^2 = 1
```

The point, inverse point, and center are collinear because:

```text
det((2,1), (2/5,1/5)) = 2*(1/5) - 1*(2/5) = 0
```

The bad row does not ask the solver to rediscover inversion. The validator
replays inversion first, then the SMT-LIB artifact checks only the final exact
linear contradiction:

```text
inverse_x = 2/5
inverse_x = 1/2
```

The second bad row follows the same boundary for the distance-product scalar:

```text
squared_radius_product = 1
squared_radius_product = 2
```
