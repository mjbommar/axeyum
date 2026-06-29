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
