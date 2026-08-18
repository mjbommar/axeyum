# Lemire half-degree irreducibility artifacts

These are finite, checked witnesses for the conjecture in Lemire and Kaser,
*Strongly universal string hashing is fast*.  They do not prove the universal
claim.

The [`range-1-400`](range-1-400/README.md) directory contains the separately
sharded, dual-checked result for every degree through 400. The standalone file
below remains a small stable gate control with the polynomial named in the
paper's discussion.

`degree-400.json` certifies

```text
x^400 + x^5 + x^3 + x^2 + 1
```

over `GF(2)`.  Its nonleading degree is 5, below `floor(400/2) = 200`.
The artifact contains the complete Frobenius reduction chain and the Rabin
Bezout obligations for the distinct prime divisors 2 and 5 of 400.
Its canonical 188,458 bytes have SHA-256
`30ae3f3377e9c66c6c2ecf00af6e4fade262b80ecd0e6a8fe4d7f597042383d5`.

Regenerate from an absent output path with the producer identity recorded in
the artifact:

```sh
cargo run --release -p axeyum-cas --bin axeyum-gf2-certify -- \
  artifacts/gf2/lemire/degree-400.json \
  lemire-degree-400 \
  axeyum-gf2-certify@b678ec7e6 \
  0,2,3,5,400
```

Check the committed bytes without running the producer:

```sh
cargo run --quiet -p axeyum-cas --bin axeyum-gf2-check -- \
  artifacts/gf2/lemire/degree-400.json
```

The repository gate runs that command.  Success requires the packed primary
checker and the independent dense-coefficient checker to accept the canonical
artifact.  Unknown fields, noncanonical JSON/hex, theorem-shape drift, resource
overruns, and altered certificate identities fail closed.
