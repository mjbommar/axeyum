# Model

The carrier is the symmetric group `S3` acting on the point set:

```text
X = {1, 2, 3}
S3 = {e, r, r2, s12, s13, s23}
```

Each group element is represented by a total map `X -> X`. The validator first
checks that each map is bijective, then interprets multiplication as function
composition:

```text
table[row][column] = row after column
```

The nontrivial maps are:

```text
r   = (1 2 3)
r2  = (1 3 2)
s12 = (1 2)
s13 = (1 3)
s23 = (2 3)
```

## Checked Data

The pack stores:

- the Cayley table for composition;
- the underlying permutation maps;
- cycle lengths for every element;
- the sign map `S3 -> {even, odd}`;
- the natural action table on `{1, 2, 3}`;
- orbit and stabilizer data for the point `1`.

## Axeyum Route

The near-term Axeyum route is finite-function replay or an EUF encoding with a
finite-domain guard. The broader group-theory route is a Lean horizon.
