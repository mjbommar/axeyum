# Model

Each witness fixes a finite universe `U` and three subsets `A`, `B`, and `C`.
The validator treats every subset as an exact set of element labels and rejects
any element not listed in `U`.

The Axeyum encoding target is a characteristic-vector view:

```text
element i in A  <=>  bit i of a is 1
A union B       <=>  a | b
A intersect B  <=>  a & b
A subset B      <=>  (a & ~b) == 0
```

The current pack stays one level above that encoding. It recomputes the same
operations with Python sets so the fixed mathematical claim is checked
independently of any search route.

## Limitations

These are fixed finite checks. Universal finite-domain identities should
graduate to Bool/BV formulas plus checked SAT/CNF evidence. Infinite sets,
power-set axioms, ordinals, cardinals, and choice principles remain
Lean-horizon material.
