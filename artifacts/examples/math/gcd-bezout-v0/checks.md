# Checks

## `gcd-common-divisors-replay`

Expected result: `sat`.

The witness states that `gcd(252, 198) = 18` and lists the positive common
divisors. The validator recomputes the gcd and enumerates the common divisors.

## `bezout-identity-replay`

Expected result: `sat`.

The witness checks:

```text
252*4 + 198*(-5) = 18
```

The validator also confirms that `18` is the gcd of `252` and `198`.

## `divisibility-quotient-replay`

Expected result: `sat`.

The witness checks:

```text
252 = 18 * 14
```

## `diophantine-gcd-obstruction`

Expected result: `unsat`.

The fixed false claim is that integers `x` and `y` satisfy:

```text
6*x + 10*y = 15
```

The validator recomputes `gcd(6, 10) = 2` and checks that `2` does not divide
`15`, which is the exact obstruction for this two-variable linear Diophantine
equation. The resource-backed Axeyum regression parses the matching QF_LIA
SMT-LIB artifact and requires independently rechecked `UnsatDiophantine`
evidence.
