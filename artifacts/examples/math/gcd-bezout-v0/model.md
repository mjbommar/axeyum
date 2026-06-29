# Model

Each check is an exact integer artifact.

```text
gcd(a, b) = d
a*x + b*y = d
dividend = divisor * quotient
a*u + b*v = target
```

The validator checks:

```text
gcd replay:        recompute gcd(abs(a), abs(b))
common divisors:   enumerate positive common divisors
Bezout witness:    recompute a*x + b*y and compare with gcd(a,b)
divisibility:      recompute divisor * quotient
Diophantine unsat: check gcd(abs(a), abs(b)) does not divide target
```

## Axeyum Route

The intended Axeyum route is QF_LIA. SAT rows replay integer models directly.
The UNSAT row should graduate to an `UnsatDiophantine` artifact: normalize the
single equation, recompute the coefficient gcd, and reject when it does not
divide the target.
