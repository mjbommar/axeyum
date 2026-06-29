# Model

The pack uses finite universes with explicitly listed predicate tables.

For a unary predicate `P` over universe `U`:

```text
forall x in U. P(x)  ==  and_{u in U} P(u)
exists x in U. P(x)  ==  or_{u in U} P(u)
```

The validator rejects predicate tables whose keys do not exactly match the
universe. For the bounded implication row, it enumerates all Boolean unary
predicate valuations over the finite universe and searches for a counterexample
to:

```text
forall x. P(x) -> exists x. P(x)
```

The binary relation row treats a relation as a Boolean predicate
`R(x, y)`. Symmetry is the finite condition:

```text
forall x y. R(x, y) -> R(y, x)
```

The example relation contains `R(a, b)` but not `R(b, a)`, so it is a checked
counterexample to symmetry.

The final row is metadata only: general first-order validity over arbitrary or
infinite domains is outside this finite replay model.
