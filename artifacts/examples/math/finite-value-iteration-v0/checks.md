# Checks

## Replay-Only Witnesses

- `mdp-table-witness`
  - Expected: `sat`
  - Replays the three states, per-state actions, rational rewards, the
    discount `1/2`, and exact probability-row sums.

- `value-iteration-witness`
  - Expected: `sat`
  - Recomputes every Bellman backup `Q(s, a) = r + gamma * P . V` and every
    greedy value `V'(s) = max_a Q(s, a)` across the three iterations from
    the zero vector.

- `bellman-fixed-point-witness`
  - Expected: `sat`
  - Checks that one full Bellman backup at `(5/2, 3, 0)` reproduces
    `(5/2, 3, 0)` exactly, with greedy policy `(a, a, a)`.

- `contraction-step-witness`
  - Expected: `sat`
  - Recomputes the sup-norm steps `3, 1/2, 0` and the single-instance
    contraction inequalities against `gamma = 1/2`.

- `bad-backup-rejected`
  - Expected: `unsat`
  - Replays the trace and rejects the malformed claim that the
    second-iteration backup `Q2(s1, a)` is `2`.

## Checked Evidence

- `qf-lra-bad-backup`
  - Expected: `unsat`
  - Source artifact:
    `artifacts/examples/math/finite-value-iteration-v0/smt2/bad-backup-farkas-conflict.smt2`
  - Route: QF_LRA/Farkas
  - Regression:
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_value_iteration_bad_backup_artifact_emits_checked_farkas`

## Horizon

- `general-mdp-theory-lean-horizon`
  - Expected: `not-run`
  - The Banach fixed-point theorem, value-iteration/policy-iteration
    convergence in general, uniqueness and optimality of the Bellman fixed
    point, greedy-policy optimality, infinite-horizon/average-reward and
    continuous MDP theory, Q-learning, and floating-point dynamic
    programming are not checked by this pack.
