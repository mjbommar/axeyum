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

## `composite-modulus-nonfield-qf-bv-drat`

Expected result: `unsat`.

The QF_BV artifact encodes the same no-inverse claim using a 3-bit residue
variable:

```text
inv < 6
(2 * inv) mod 6 = 1
```

The product is computed at 6-bit width before `bvurem 6`, so this is an exact
fixed-width encoding of the residue equation for the listed finite domain. The
solver regression exports the bit-blasted CNF with a DRAT refutation and
rechecks the certificate independently.
