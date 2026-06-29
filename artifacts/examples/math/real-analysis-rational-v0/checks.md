# Checks

## `nested-rational-neighborhood-witness`

Checks that `[1/4, 3/4]` is contained in the open ball centered at `1/2` with
radius `1/3`. The validator verifies every listed sample point and the maximum
endpoint distance.

## `linear-epsilon-delta-rational-witness`

Checks a finite epsilon-delta sample for `f(x) = 2x + 1` at `0`. The validator
recomputes which sample points are inside `|x| < 1/2` and checks the output
distance is strictly below `1`.

## `squeeze-polynomial-bound-witness`

Checks the finite polynomial side condition:

```text
|x| <= 1/10 -> x^2 <= 1/100 and |x^3| <= 1/1000
```

for the listed rational samples.

## `bad-linear-delta-rejected`

Rejects the false claim that `delta = 3/4` works for the linear epsilon-delta
row. The checked counterexample is `x = 2/3`.

## `general-real-analysis-lean-horizon`

Records that fully quantified real-analysis facts need Lean reconstruction.
The bounded rational rows do not prove general continuity, completeness, or
limit laws.
