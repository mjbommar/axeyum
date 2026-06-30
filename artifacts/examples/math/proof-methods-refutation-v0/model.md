# Model

For `PHP(n,m)`, introduce one Boolean variable:

```text
x_p_h = pigeon p is assigned to hole h
```

Constraints:

- every pigeon is assigned to at least one hole;
- no pigeon is assigned to two different holes;
- no two pigeons share the same hole.

`PHP(3,2)` is UNSAT because three distinct pigeons cannot inject into two
holes. `PHP(2,2)` is SAT and serves as a witness-replay control case.

## Encoding Sketch

For every pigeon `p`:

```text
or_h x_p_h
```

For every pigeon `p` and distinct holes `h1`, `h2`:

```text
not (x_p_h1 and x_p_h2)
```

For every hole `h` and distinct pigeons `p1`, `p2`:

```text
not (x_p1_h and x_p2_h)
```

The finite model is purely propositional, so the intended Axeyum route is
Bool/SAT followed by a checked SAT proof for the UNSAT case. This pack now
keeps the source-level `PHP(3,2)` DIMACS artifact under `cnf/` and routes it
through the Boolean DRAT/LRAT regression in addition to validator-side finite
truth-table enumeration.
