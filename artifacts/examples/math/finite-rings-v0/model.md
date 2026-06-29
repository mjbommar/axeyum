# Model

Each ring witness lists one carrier and two Cayley tables:

```text
add[row][col] = row_element + col_element
mul[row][col] = row_element * col_element
```

The validator checks:

```text
addition:       abelian group with zero
multiplication: closure and associativity
distributivity: a*(b+c) = a*b + a*c and (a+b)*c = a*c + b*c
one:            optional two-sided multiplicative identity
zero divisor:   nonzero a,b with a*b = 0
```

## Axeyum Route

The intended Axeyum route is bounded BV/enumeration over table indices. The
current pack stays at independent finite-table replay.
