# Checks

## `successor-addition-replay`

Expected result: `sat`.

The witness checks:

```text
5 + S(7) = 13
S(5 + 7) = 13
```

## `addition-commutativity-fixed`

Expected result: `sat`.

The witness checks:

```text
6 + 4 = 4 + 6 = 10
```

## `multiplication-distributivity-fixed`

Expected result: `sat`.

The witness checks:

```text
2 * (3 + 4) = 2*3 + 2*4 = 14
```

## `successor-injective-bounded`

Expected result: `unsat`.

The fixed false claim is that bounded naturals `x,y <= 7` can satisfy:

```text
S(x) = S(y)
x != y
```

## `zero-not-successor-bounded`

Expected result: `unsat`.

The fixed false claim is that some bounded natural `n <= 7` satisfies:

```text
S(n) = 0
```

## `bounded-natural-negative-rejected`

Expected result: `unsat`.

The fixed false claim is that the bounded natural domain `0..7` contains a
negative element.
