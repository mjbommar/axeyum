# Model

The source object is the exact rational quadratic:

```text
f(x) = x^2
```

The committed Wolfe line-search witness starts at:

```text
x0 = 1
gradient = 2
direction = -2
initial directional derivative = -4
c1 = 1/4
c2 = 1/2
```

Along the line `x(alpha) = 1 - 2*alpha`, the exact minimizer is:

```text
alpha = 1/2
x(alpha) = 0
f(x(alpha)) = 0
directional derivative at alpha = 0
```

The Wolfe sufficient-decrease right-hand side is:

```text
f(1) + c1 * alpha * phi'(0)
= 1 + (1/4) * (1/2) * (-4)
= 1/2
```

So the accepted step has Armijo/Wolfe sufficient-decrease slack:

```text
1/2 - 0 = 1/2
```

The Wolfe curvature bound is:

```text
|phi'(alpha)| <= c2 * |phi'(0)|
0 <= (1/2) * 4
```

The checked bad row tests the full step `alpha = 1`. Exact replay gives:

```text
x(1) = -1
gradient = -2
phi'(1) = gradient * direction = 4
c2 * |phi'(0)| = 2
curvature violation = 4 - 2 = 2
```

This is a single exact replay check. It does not prove Wolfe existence,
Zoutendijk convergence, global convergence rates, nonconvex line-search
behavior, or floating-point behavior.
