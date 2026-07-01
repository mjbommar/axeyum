# Checks

## `crt-coprime-witness`

Expected result: `sat`.

The documented witness `x = 8` satisfies the two congruences modulo coprime
moduli `3` and `5`.

## `modular-inverse-witness`

Expected result: `sat`.

The documented inverse `5` satisfies `3 * 5 == 1 (mod 7)`.

## `composite-nonunit-no-inverse`

Expected result: `unsat`.

The claim "there exists an inverse for `2` modulo `6`" is false. The validator
checks every candidate residue modulo `6`.

## `qf-lia-nonunit-diophantine`

Expected result: `unsat`.

The SMT-LIB artifact encodes the same non-unit inverse question as
`2*b - 6*k = 1` over integers. Axeyum emits and checks an
`UnsatDiophantine` certificate: `gcd(2,6) = 2` does not divide `1`.

## `qf-lia-incompatible-crt-diophantine`

Expected result: `unsat`.

The fixed false CRT claim is:

```text
x == 1 mod 4
x == 2 mod 6
```

Writing the two congruences as `x = 1 + 4*a` and `x = 2 + 6*b` gives:

```text
4*a - 6*b = 1
```

Axeyum emits and checks an `UnsatDiophantine` certificate:
`gcd(4,6) = 2` does not divide `1`.

## `fermat-units-mod-prime`

Expected result: `unsat`.

The checked query is the absence of a counterexample to `a^4 == 1 (mod 5)` over
the units modulo `5`. This is finite exhaustive replay, not a general Fermat
theorem certificate.
