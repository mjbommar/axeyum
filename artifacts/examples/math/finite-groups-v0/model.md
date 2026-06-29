# Model

Each operation is a finite Cayley table over an explicit carrier. Rows and
columns are indexed by the carrier order:

```text
table[row_index][column_index] = row_element * column_element
```

The validator checks:

```text
closure:       every table entry is in the carrier
identity:      e*x = x and x*e = x
inverse:       for every x, some y has x*y = e and y*x = e
associativity: (x*y)*z = x*(y*z) for all triples
```

## Axeyum Route

The intended Axeyum route is either a finite BV encoding of table indices or an
EUF-style operation symbol with explicit finite-domain constraints. The current
pack stays at independent finite-table replay.
