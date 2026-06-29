# Model

## Order

The carrier is the powerset of `{a,b}` encoded as:

```text
0, A, B, AB
```

The order is subset inclusion:

```text
0 <= A
0 <= B
A <= AB
B <= AB
```

plus reflexive pairs. The validator checks reflexivity, antisymmetry, and
transitivity directly from the pair set.

## Lattice Operations

Meet is intersection and join is union:

```text
A meet B = 0
A join B = AB
A meet AB = A
B join 0 = B
```

The validator recomputes lower and upper bound sets from the relation and then
checks that every listed meet is the unique greatest lower bound and every
listed join is the unique least upper bound.

## Distributivity

The finite lattice is distributive:

```text
x meet (y join z) = (x meet y) join (x meet z)
x join (y meet z) = (x join y) meet (x join z)
```

The validator checks both equations for every triple.

## Monotone Map

The map `f(x) = x join A` is encoded as:

```text
0  -> A
A  -> A
B  -> AB
AB -> AB
```

The fixed points are:

```text
A, AB
```

The validator checks monotonicity and confirms that `A` is the least fixed
point in the finite order.
