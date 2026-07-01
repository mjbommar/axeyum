# Checks

## `crt-compatible-noncoprime-witness`

Expected result: `sat`.

The witness checks:

```text
x = 8
x == 2 mod 6
x == 8 mod 10
```

The moduli are not coprime, but the remainders agree modulo `gcd(6,10) = 2`.

## `quadratic-residue-witness`

Expected result: `sat`.

The witness checks:

```text
4^2 == 5 mod 11
```

## `quadratic-nonresidue-rejected`

Expected result: `unsat`.

The fixed false claim is that some residue `x` satisfies:

```text
x^2 == 3 mod 7
```

The validator enumerates all residues modulo `7`.

## `quadratic-nonresidue-qf-bv-drat`

Expected result: `unsat`.

The QF_BV artifact encodes the same nonresidue claim using a 3-bit residue
variable:

```text
x < 7
(x * x) mod 7 = 3
```

The product is computed at 6-bit width before `bvurem 7`, so this is an exact
fixed-width encoding of the residue equation for the listed finite domain. The
solver regression exports the bit-blasted CNF with a DRAT refutation and
rechecks the certificate independently.

## `bad-square-witness-rejected`

Expected result: `unsat`.

The fixed false claim is that `2` is a square root of `2` modulo `7`:

```text
2^2 == 2 mod 7
```

The validator recomputes `2^2 mod 7 = 4` and rejects the malformed witness.

## `bad-square-witness-qf-bv-drat`

Expected result: `unsat`.

The QF_BV artifact computes the same bad witness at fixed width:

```text
(2 * 2) mod 7 = 4
(2 * 2) mod 7 = 2
```

The product is computed at 6-bit width before `bvurem 7`. The route test
exports the bit-blasted CNF with a DRAT refutation and rechecks the certificate
independently.

## `sum-two-squares-witness`

Expected result: `sat`.

The witness checks:

```text
65 = 1^2 + 8^2
```

## `sum-two-squares-mod4-rejected`

Expected result: `unsat`.

The fixed false claim is that integers `a,b` satisfy:

```text
7 = a^2 + b^2
```

Squares modulo `4` are only `0` or `1`, so a sum of two squares cannot be
congruent to `3 mod 4`.

## `bounded-diophantine-witness`

Expected result: `sat`.

The witness checks:

```text
14*(-1) + 21*1 = 7
```

## `diophantine-gcd-obstruction-qf-lia`

Expected result: `unsat`.

The fixed false claim is that integers `x,y` satisfy:

```text
14*x + 21*y = 5
```

The validator recomputes `gcd(14,21) = 7` and checks that `7` does not divide
`5`. The QF_LIA artifact encodes the same linear equation, and the route test
requires checked `UnsatDiophantine` evidence.
