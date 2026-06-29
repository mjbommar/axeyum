# Model

The finite model is ordinary integer arithmetic modulo a small positive modulus.

Notation:

```text
x == r (mod m)  iff  m divides (x - r)
a has inverse b modulo m  iff  a * b == 1 (mod m)
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

### Fermat-Style Unit Check

For every unit `a` modulo prime `5`, the validator confirms:

```text
a^4 == 1 (mod 5)
```

This is a finite check of a small prime modulus, not a general theorem proof.
