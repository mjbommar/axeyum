# End To End: Bounded Dynamics And Operators

This lesson follows bounded analysis-adjacent resources from data row to
replayed result. It uses
[bounded-dynamics-v0](../../../artifacts/examples/math/bounded-dynamics-v0/) and
[finite-operator-v0](../../../artifacts/examples/math/finite-operator-v0/),
the finite Chebyshev-system slice in
[finite-chebyshev-systems-v0](../../../artifacts/examples/math/finite-chebyshev-systems-v0/),
with the finite stochastic transition slice in
[finite-markov-chain-v0](../../../artifacts/examples/math/finite-markov-chain-v0/),
the finite hitting-time slice in
[finite-hitting-times-v0](../../../artifacts/examples/math/finite-hitting-times-v0/),
and the finite spectral slice in
[spectral-linear-algebra-v0](../../../artifacts/examples/math/spectral-linear-algebra-v0/).
For a focused bounded recurrence and invariant trace, read
[End To End: Bounded Recurrence Dynamics](bounded-dynamics-end-to-end.md).
For a focused finite recurrence and Euler-step trace, read
[End To End: Finite Dynamics And Euler Replay](finite-dynamics-euler-end-to-end.md).
For a focused finite Euler transition and error-table trace, read
[End To End: Finite Euler Method](finite-euler-method-end-to-end.md).
For a focused finite-dimensional operator and norm-bound trace, read
[End To End: Finite-Dimensional Operators](finite-operator-end-to-end.md).
For the cross-pack operator/Chebyshev query map, read
[Chebyshev And Operator Replay Index](chebyshev-operator-index.md).

Concept rows:

- `field_differential_equations_and_dynamical_systems`,
  `field_functional_analysis_and_operator_theory`, `field_numerical_analysis`,
  and `field_linear_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `bounded-invariant-witness` | `sat` | replay-only |
| `unsafe-threshold-reachable` | `sat` | replay-only |
| `bad-transition-step-rejected` | `unsat` | checked |
| `bad-threshold-step-rejected` | `unsat` | checked |
| `bad-invariant-bound-rejected` | `unsat` | checked |
| `finite-horizon-distribution-replay` | `sat` | replay-only |
| `stationary-distribution-witness` | `sat` | replay-only |
| `bad-stochastic-row-rejected` | `unsat` | replay-only |
| `qf-lra-bad-stochastic-row` | `unsat` | checked |
| `bad-stationary-distribution-rejected` | `unsat` | replay-only |
| `qf-lra-bad-stationary-distribution` | `unsat` | checked |
| `first-hit-distribution-witness` | `sat` | replay-only |
| `absorption-probability-equations` | `sat` | replay-only |
| `expected-hitting-time-equations` | `sat` | replay-only |
| `bad-expected-time-rejected` | `unsat` | replay-only |
| `qf-lra-bad-expected-time` | `unsat` | checked |
| `matrix-operator-bound` | `sat` | replay-only |
| `bad-l1-sum-norm-rejected` | `unsat` | checked |
| `bad-operator-bound-rejected` | `unsat` | checked |
| `chebyshev-recurrence-witness` | `sat` | replay-only |
| `bad-chebyshev-t3-rejected` | `unsat` | checked |
| `vandermonde-unisolvence-witness` | `sat` | replay-only |
| `interpolation-polynomial-witness` | `sat` | replay-only |
| `alternating-residual-witness` | `sat` | replay-only |
| `bad-duplicate-node-grid-rejected` | `unsat` | checked |
| `bad-interpolation-sample-rejected` | `unsat` | checked |
| `bad-max-error-bound-rejected` | `unsat` | checked |
| `spectral-decomposition-witness` | `sat` | replay-only |

These are bounded finite traces and finite-dimensional algebra checks, not
general analysis theorems.

## Encode

The invariant witness is a fixed recurrence trace:

```text
x(0) = 0
x(t+1) = x(t) + 2
trace = 0, 2, 4, 6, 8
invariant = 0 <= x(t) <= 8
```

The operator witness is a fixed matrix-vector calculation:

```text
A = [[1,-1],
     [2, 1]]
x = [2,-1]
A*x = [3,3]
||x||_infty = 2
||A||_row-sum = 3
||A*x||_infty = 3
```

The finite Chebyshev-system witness is a fixed polynomial sample grid:

```text
x = -1, 0, 1
basis = 1, x, x^2
det([[1,-1,1], [1,0,0], [1,1,1]]) = 2
```

## Replay

For the dynamics row, the checker verifies every transition:

```text
0 -> 2 -> 4 -> 6 -> 8
```

and then checks every state lies in `[0,8]`.

The bad transition-step row reuses that exact trace but claims the step after
state `2` lands at `5`; exact replay computes `2 + 2 = 4`, then the source
QF_LRA artifact checks the contradictory next-state equality through Farkas
evidence. The bad invariant-bound row reuses the same trace but claims every
state is at most `6`; exact replay computes terminal/max state `8`, then the
source QF_LRA artifact checks `terminal_state = 8` with `terminal_state <= 6`
through Farkas evidence.

The bad threshold-step row uses the plus-three threshold trace but claims step
`2` already reaches threshold `7`; exact replay computes state `6`, so the
source QF_LRA artifact checks `state_at_claimed_step = 6`, `threshold = 7`,
and `state_at_claimed_step >= threshold` through Farkas evidence.

For the operator/norm rows, the checker recomputes `u+v`, `A*x`, the `l1` and
infinity norms, the row-sum norm, and the bound:

```text
||u+v||_1 = 5 <= 3 + 4
||A*x||_infty = 3 <= 3 * 2 = 6
```

The bad norm row reuses the exact vector replay but claims `||u+v||_1 <= 4`;
the bad-bound row reuses the same exact matrix-vector replay but claims
`||A*x||_infty <= 2`. Exact replay computes `5` and `3`, then the source
QF_LRA artifacts check the final contradictions through Farkas evidence.

For the Chebyshev row, it checks the finite recurrence at `x = 1/2`:

```text
T0 = 1
T1 = 1/2
T2 = -1/2
T3 = -1
```

The bad Chebyshev-prefix row reuses that finite recurrence replay and rejects
the malformed value `T3 = -1/2` through checked Farkas evidence.

For the finite Chebyshev-system rows, it checks exact finite unisolvence and
interpolation:

```text
p(x) = 2 - x + 3*x^2
p(-1), p(0), p(1) = 6, 2, 4
r(x) = x^2 - 1/2
r(-1), r(0), r(1) = 1/2, -1/2, 1/2
```

It also rejects a duplicate-node grid by recomputing determinant `0` and a
nonzero null vector, then checks the final false determinant-`1` claim through
QF_LRA/Farkas evidence. The same pack rejects a false interpolation sample by
replaying `p(1)=4` and checking the malformed `p(1)=5` claim through the same
Farkas route, and rejects a false alternation uniform-error claim by replaying
common residual magnitude `1/2` before checking the malformed `2/3` claim.

For the Markov-chain row, it checks exact stochastic evolution:

```text
[1,0,0] * P = [1/2,1/2,0]
[1/2,1/2,0] * P = [1/4,1/2,1/4]
```

The malformed transition and stationary rows are replayed first, then separate
`qf-lra-*` rows check the row-sum and stationary-coordinate contradictions
through Farkas evidence.

For a fuller trace of the Markov-chain rows, read
[End To End: Finite Markov Chains](finite-markov-chain-end-to-end.md).

For the hitting-time row, it carries only not-yet-hit mass forward:

```text
P(T = 2) = 1/4
P(T = 3) = 1/4
P(T = 4) = 3/16
P(T > 4) = 5/16
h(start) = 1 + 1/2*h(start) + 1/2*h(middle) = 4
```

For a fuller trace of the hitting-time rows, read
[End To End: Finite Hitting Times](finite-hitting-times-end-to-end.md).

For the spectral row, it checks exact rational eigenpair and decomposition
arithmetic:

```text
A*[1,1] = 3*[1,1]
P*D*P^-1 = A
```

For a fuller trace of the spectral rows, read
[End To End: Spectral Linear Algebra](spectral-linear-algebra-end-to-end.md).

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_dynamics_bad_transition_step_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_dynamics_bad_threshold_step_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes bounded_dynamics_bad_invariant_bound_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-euler-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_euler_bad_max_error_bound_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-markov-chain-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-hitting-times-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_operator_bad_l1_sum_norm_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_operator_bad_operator_bound_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_operator_bad_chebyshev_t3_artifact_emits_checked_farkas
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chebyshev-systems-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/spectral-linear-algebra-v0
```

Expected output for each command:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

The trusted checker handles finite traces, exact rational matrices, and finite
recurrence lists. General limits, ODE existence and uniqueness, stability,
compact operators, Banach/Hilbert-space theorems, general Chebyshev spaces,
Haar-space theorems, and minimax approximation remain Lean-horizon material.
Infinite-dimensional spectral theory,
infinite-state Markov chains, recurrence/transience classifications, optional
stopping, and mixing-time theorems also remain proof-horizon material.
