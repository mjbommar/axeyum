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

The Axeyum route is bounded BV/enumeration over table indices. The satisfiable
`Z/4Z` rows still use independent finite-table replay. The bad distributivity
row now also carries a QF_BV artifact for the failing triple `(1,0,0)`:

```text
left distributivity wants: a*(b+c) = (a*b)+(a*c)
source table computes:     1       = 0
```

The SMT-LIB artifact encodes this table-derived conflict as a one-bit BV
contradiction so the generated CNF can be refuted by checked DRAT evidence.
