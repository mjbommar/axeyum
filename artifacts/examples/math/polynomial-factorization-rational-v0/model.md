# Model

Polynomials are encoded as coefficient lists in ascending degree order:

```text
[a0, a1, a2] = a0 + a1*x + a2*x^2
```

The finite checker performs exact rational arithmetic only. It normalizes
trailing zero coefficients, multiplies factor lists, runs polynomial long
division, computes monic Euclidean GCDs, and differentiates coefficient lists
for the square-free row.

The irreducibility contrast is deliberately small:

```text
p(x) = x^2 + 1
discriminant = -4
```

A negative discriminant rules out rational linear factors for this fixed
quadratic. General irreducibility, unique factorization, algebraic closure, and
factorization algorithms over arbitrary fields remain proof-assistant and
library-boundary work.
