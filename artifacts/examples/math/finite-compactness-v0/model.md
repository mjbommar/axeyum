# Model

The finite topology uses the universe:

```text
U = {a,b,c}
```

with the discrete topology, so every subset of `U` is open and closed.

## Open Cover

The cover is:

```text
{a,b}, {b,c}, {a,c}
```

The listed subcover is:

```text
{a,b}, {b,c}
```

The validator recomputes both unions and checks that they cover `U`.

## Minimal Subcover

The validator enumerates all subfamilies of size less than `2` and confirms
none cover `U`. It then checks the listed two-set subcover covers `U`.

## Finite Intersection Family

The closed family is:

```text
{a,b}, {b,c}, {b}
```

Every non-empty finite subfamily has non-empty intersection, and the total
intersection is:

```text
{b}
```

The validator checks this directly by finite enumeration.

## Bad Cover

The bad cover is:

```text
{a}, {b}
```

Its union misses `c`, so the open-cover claim is rejected by exact finite-set
arithmetic.

The final Boolean contradiction is:

```text
c_covered = false
c_covered = true
```

The pack keeps that contradiction on the checked `Bool/CNF` DRAT/LRAT route.
