# Checks

## `signed-trichotomy-fixed`

Expected result: `sat`.

The witness checks that exactly one relation holds for `-3` and `4`, namely:

```text
-3 < 4
```

## `order-transitivity-fixed`

Expected result: `sat`.

The witness checks:

```text
-2 < 1 < 5
-2 < 5
```

## `integer-ring-identity-replay`

Expected result: `sat`.

The witness checks:

```text
(-7 + 5) - 5 = -7
```

## `linear-equation-witness`

Expected result: `sat`.

The witness checks:

```text
3*3 - 2*1 = 7
```

## `integer-interval-infeasible`

Expected result: `unsat`.

The fixed false claim is that some integer `z` satisfies:

```text
z >= 5
z <= 2
```

## `diophantine-gcd-obstruction`

Expected result: `unsat`.

The fixed false claim is that integers `x,y` satisfy:

```text
2*x + 4*y = 3
```

The validator checks the exact GCD obstruction: `gcd(2,4) = 2` and `2` does
not divide `3`.
