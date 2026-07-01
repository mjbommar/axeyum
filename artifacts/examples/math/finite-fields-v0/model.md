# Model

Each check works in the residue set `{0, ..., n-1}` with operations:

```text
a + b = (a + b) mod n
a * b = (a * b) mod n
```

For a prime modulus `p`, the nonzero residues form the multiplicative group of
the finite field `F_p`. The inverse-table witness lists one inverse for each
nonzero residue.

For a composite modulus, the same residue arithmetic is still a finite ring, but
nonzero elements can fail to have inverses. The `Z/6Z` check focuses on `2`,
which has no multiplicative inverse because every product `2*b mod 6` is even.

## Axeyum Route

The intended Axeyum route is bounded BV/enumeration:

```text
forall a != 0 in F_p, exists inv. (a * inv) mod p = 1
not exists b in Z/6Z. (2 * b) mod 6 = 1
bad candidate in F_7: (3 * 4) mod 7 = 5, not 1
```

The satisfiable inverse-table row still uses direct finite replay. The
composite-modulus no-inverse row now also carries a QF_BV artifact: a 3-bit
residue `inv` is guarded by `inv < 6`, zero-extended to 6 bits, multiplied by
`2`, reduced by `bvurem 6`, and constrained to equal `1`. The generated CNF is
refuted by checked DRAT evidence.

The bad prime-field inverse-candidate row carries a second QF_BV artifact:
`3*4` is computed at 6-bit product width, reduced modulo `7`, constrained to
the replayed value `5`, and also constrained to the false inverse target `1`.
The generated CNF is likewise refuted by checked DRAT evidence.
