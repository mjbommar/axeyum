# Model

The data model is deliberately finite.

## Bivariate Polynomials

A two-variable polynomial is a list of monomial objects:

```json
{"coeff": "2", "x_power": 1, "y_power": 1}
```

This denotes `2xy`. Coefficients are exact rational strings and powers are
non-negative integers. The validator differentiates monomials symbolically:

```text
d/dx (c*x^i*y^j) = c*i*x^(i-1)*y^j
d/dy (c*x^i*y^j) = c*j*x^i*y^(j-1)
```

It then evaluates the resulting polynomial at the listed rational point.

## Matrices

Jacobians and Hessians are exact rational matrices. Matrix multiplication uses
the same small arithmetic kernel as the existing linear-algebra packs.

The chain-rule row checks:

```text
J(h o g)(p) = J_h(g(p)) * J_g(p)
```

for one fixed polynomial inner map `g` and one fixed polynomial outer map `h`.

## Horizon

The pack does not claim general differentiability. Limit-based definitions,
normed-space chain rules, inverse and implicit function theorems, and manifold
calculus remain Lean-horizon.
