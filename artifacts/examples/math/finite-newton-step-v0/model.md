# Model

The source polynomial is:

```text
f(x,y) = x^2 + x*y + 2*y^2 - 4*x - 6*y
```

The gradient and Hessian are:

```text
grad f(x,y) = [2*x + y - 4, x + 4*y - 6]
H = [[2, 1],
     [1, 4]]
```

At the start point `x0 = [0,0]`:

```text
f(x0) = 0
grad f(x0) = [-4, -6]
-grad f(x0) = [4, 6]
```

Solving the Newton system:

```text
[[2,1],[1,4]] * [10/7,8/7] = [4,6]
```

So:

```text
direction = [10/7, 8/7]
next = [10/7, 8/7]
grad f(next) = [0,0]
f(next) = -44/7
decrease = 44/7
```

The positive-definite shadow is the two-by-two Sylvester check:

```text
leading principal minors = [2, 7]
```

Those finite checks make the listed step replayable. They do not prove a
general theorem about Newton's method.
