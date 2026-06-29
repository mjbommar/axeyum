# Model

The pack models proof methods as small Boolean obligations.

For direct proof, the checker replays:

```text
p = true
q = true
p -> q = true
therefore q = true
```

For no-counterexample rows, the checker enumerates all assignments over the
listed variables and rejects any assignment violating the proof pattern:

```text
contrapositive: (p -> q) == (!q -> !p)
cases:          (p -> r) and (!p -> r) imply r
contradiction:  p and (p -> q) and !q is unsatisfiable
```

For the invalid converse, the checker accepts the row only because it finds a
counterexample:

```text
p = false
q = true
p -> q = true
q -> p = false
```

## Limitations

The examples are fixed finite Boolean artifacts. They teach the executable
shape of proof methods, but they do not certify a general proof calculus or
Lean reconstruction route.
