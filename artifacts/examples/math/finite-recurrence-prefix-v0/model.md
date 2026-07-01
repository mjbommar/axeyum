# Model

The pack uses exact rational values.

## Fibonacci Prefix

```text
F_0 = 0
F_1 = 1
F_n = F_{n-1} + F_{n-2}
prefix = 0, 1, 1, 2, 3, 5, 8
```

## Affine Prefix

```text
x_0 = 0
x_{n+1} = 2*x_n + 1
prefix = 0, 1, 3, 7, 15
```

## Companion Matrix

```text
A = [[1, 1],
     [1, 0]]

A * [F_{n+1}, F_n]^T = [F_{n+2}, F_{n+1}]^T
```

The committed witness checks:

```text
[1,0] -> [1,1] -> [2,1] -> [3,2] -> [5,3] -> [8,5]
```

## Bad Fibonacci Row

Exact replay computes `F_6 = 8`. The checked bad row asserts `F_6 = 9` over the
same source artifact, producing a tiny QF_LRA/Farkas contradiction.

## Bad Affine Step Row

Exact affine recurrence replay computes:

```text
x_4 = 2*x_3 + 1 = 2*7 + 1 = 15
```

The checked bad row asserts the malformed claim `x_4 = 14`, leaving residual
`1`. The source artifact checks that this positive residual cannot also be
nonpositive.
