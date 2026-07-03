# Model

The model is a fixed finite perceptron training trace over integer data.

## Classes And Labels

```text
positive -> label +1
negative -> label -1
```

## Augmented Coordinates

Each training point carries a constant bias component:

```text
x = (x1, x2, 1)
```

so the learned hyperplane `w . x = 0` includes its offset in the third weight
coordinate and no separate bias update rule is needed.

## Perceptron Rule

Present a point `x` with label `y` against the current weights `w`:

```text
score   = w . x
mistake = (y * score <= 0)
w'      = w + y * x   if mistake
w'      = w           otherwise
```

Every quantity is an integer here, so the whole trace is exact rational
arithmetic. No floating-point tolerance is used.

## Fixed Trace

From `w = (0, 0, 0)` with points presented in the order
`p1, n1, p2, n2`:

```text
step 1: p1 = (1, 2, 1),  y = +1: score = 0,  y*score = 0  -> update
        w = (0,0,0) + (1,2,1) = (1, 2, 1)
step 2: n1 = (2, -1, 1), y = -1: score = 1,  y*score = -1 -> update
        w = (1,2,1) - (2,-1,1) = (-1, 3, 0)
step 3: p2 = (2, 3, 1),  y = +1: score = 7,  y*score = 7  -> keep
step 4: n2 = (1, -2, 1), y = -1: score = -7, y*score = 7  -> keep
```

Final weights `(-1, 3, 0)` after exactly `2` updates.

## Convergence Pass And Margins

Functional margins `y * (w . x)` at the final weights:

```text
p1: +1 * ((-1)*1 + 3*2 + 0*1)  = 5
n1: -1 * ((-1)*2 + 3*(-1) + 0) = 5
p2: +1 * ((-1)*2 + 3*3 + 0)    = 7
n2: -1 * ((-1)*1 + 3*(-2) + 0) = 7
```

All margins are strictly positive with minimum `5`, so a further full pass
makes no updates. Geometric margins would divide by `||w|| = sqrt(10)` and
stay outside this pack.
