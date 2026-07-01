# Model

The positive example maps one two-point Sierpinski space to a renamed copy:

```text
X = {0,1}
open_X = {}, {1}, {0,1}
Y = {u,v}
open_Y = {}, {v}, {u,v}
f(0) = u
f(1) = v
```

For every open set in `Y`, the checker recomputes the preimage under `f`:

```text
preimage({}) = {}
preimage({v}) = {1}
preimage({u,v}) = {0,1}
```

All of these are open in `X`, so the map is continuous.

## Homeomorphism

The map is bijective. Its inverse is:

```text
g(u) = 0
g(v) = 1
```

The checker applies the same finite preimage rule to `g`. Since the inverse is
also continuous, the map is a finite homeomorphism witness.

## Bad Continuity Claim

The rejected map keeps the Sierpinski topology on `X` but gives `Y` the
discrete topology:

```text
open_Y = {}, {u}, {v}, {u,v}
```

The preimage of the open set `{u}` is `{0}`, which is not open in `X`. The
checker uses this finite counterexample to reject both the continuity claim and
the homeomorphism claim.

The `qf-uf-bad-preimage-membership` proof-route artifact isolates the
function/preimage part: `f(0)=u` and `u` is in the codomain open set force `0`
to be in the preimage. A malformed preimage table that excludes `0` is rejected
by checked Alethe evidence; the fact that `{0}` is not domain-open remains an
exact finite-topology replay.
