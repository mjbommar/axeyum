# Model

The finite model is ordinary integer arithmetic modulo a small positive modulus.

Notation:

```text
x == r (mod m)  iff  m divides (x - r)
a has inverse b modulo m  iff  a * b == 1 (mod m)
CRT compatibility for r1 mod m1 and r2 mod m2 requires gcd(m1,m2) | (r2-r1)
```

## Checks

### CRT Witness

For coprime moduli `3` and `5`, the witness `x = 8` satisfies:

```text
8 == 2 (mod 3)
8 == 3 (mod 5)
```

### Modular Inverse

The witness `5` is an inverse of `3` modulo `7`:

```text
3 * 5 == 15 == 1 (mod 7)
```

### Composite Non-Unit

The residue `2` has no inverse modulo `6`.

The validator checks every candidate `b` in `[0, 6)` and confirms:

```text
2 * b != 1 (mod 6)
```

The promoted fixed-width QF_BV row uses the same finite search with a 3-bit
candidate and 6-bit product:

```text
b < 6
(2*b) mod 6 = 1
```

The bit-blasted formula is unsatisfiable and its DIMACS/DRAT refutation is
rechecked independently.

### Fermat-Style Unit Check

For every unit `a` modulo prime `5`, the validator confirms:

```text
a^4 == 1 (mod 5)
```

This is a finite check of a small prime modulus, not a general theorem proof.
The promoted QF_BV row uses a 3-bit residue guard `0 < a < 5` and a 9-bit
power computation so the largest listed unit power, `4^4 = 256`, is exact
before reducing modulo `5`.

### Incompatible CRT Pair

The pair:

```text
x == 1 (mod 4)
x == 2 (mod 6)
```

would require `4*a - 6*b = 1`. Since `gcd(4,6) = 2` does not divide `1`, the
QF_LIA artifact is unsatisfiable and the `UnsatDiophantine` certificate
rechecks the obstruction.
