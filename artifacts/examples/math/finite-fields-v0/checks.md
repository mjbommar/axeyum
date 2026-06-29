# Checks

## `prime-field-inverse-table`

Expected result: `sat`.

The witness lists inverses for every nonzero residue modulo `7`. The validator
checks primality of the modulus, residue bounds, table coverage, and
`a * inv(a) = 1 mod 7` for each nonzero `a`.

## `prime-field-distributivity-no-counterexample`

Expected result: `unsat`.

The checked query is the existence of a distributivity counterexample in `F_5`:

```text
a * (b + c) != a*b + a*c
```

The validator enumerates all `5^3` triples and confirms no counterexample
exists.

## `composite-modulus-nonfield`

Expected result: `unsat`.

The checked query is the existence of an inverse for `2` modulo `6`. The
validator enumerates all residues and confirms none multiply with `2` to
`1 mod 6`.
