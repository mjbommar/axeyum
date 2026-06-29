# Model

Each check is an exact integer artifact.

```text
exactly one of a < b, a = b, a > b
a < b and b < c implies a < c
(a + b) - b = a
sum_i coefficient_i * solution_i = target
lower <= z <= upper
```

The validator checks:

```text
trichotomy:       exactly one comparison relation holds
transitivity:     fixed chain and implied endpoint order
ring identity:    exact integer addition/subtraction replay
linear witness:   exact dot-product replay
interval unsat:    lower bound exceeds upper bound
Diophantine unsat: gcd(coefficients) does not divide target
```

## Axeyum Route

The intended Axeyum route is `QF_LIA`: SAT rows replay integer models directly,
and UNSAT rows graduate to checked integer-prelude evidence.
