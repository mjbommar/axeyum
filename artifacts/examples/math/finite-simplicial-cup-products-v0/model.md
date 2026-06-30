# Finite Model

The resource uses ordered simplices with vertex order:

```text
a < b < c
```

The main cup-product witness is the filled triangle:

```text
[a], [b], [c], [a,b], [a,c], [b,c], [a,b,c]
```

Two 1-cochains over `F2` are listed on every edge:

```text
alpha([a,b]) = 1   beta([a,b]) = 0
alpha([a,c]) = 0   beta([a,c]) = 0
alpha([b,c]) = 0   beta([b,c]) = 1
```

The Alexander-Whitney split gives:

```text
(alpha cup beta)([a,b,c]) = alpha([a,b]) * beta([b,c]) = 1
(beta cup alpha)([a,b,c]) = beta([a,b]) * alpha([b,c]) = 0
```

The Leibniz witness uses two 0-cochains on the three-edge complex:

```text
f(a)=1, f(b)=0, f(c)=1
g(a)=1, g(b)=1, g(c)=0
```

The validator recomputes `f cup g`, `delta f`, `delta g`, `delta(f cup g)`,
`delta f cup g`, `f cup delta g`, and the F2 sum of those two cup terms.

The QF_BV artifact isolates the final malformed value as one-bit arithmetic:

```text
cup_abc = alpha_ab AND beta_bc
alpha_ab = 1
beta_bc = 1
cup_abc = 0
```
