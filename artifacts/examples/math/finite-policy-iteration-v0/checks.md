# Checks

## Replay-Only Witnesses

- `mdp-policy-table-witness`
  - Expected: `sat`
  - Replays the three states, per-state actions, rational rewards, the
    discount `1/2`, exact probability-row sums, and the well-formedness of
    the three committed policies.

- `policy-evaluation-witness`
  - Expected: `sat`
  - Substitutes each committed value vector back into its policy's
    fixed-point equation `V = r_pi + gamma * P_pi * V` and requires an
    exact zero residual: `(2, 2/3, 0)`, `(2, 3, 0)`, `(5/2, 3, 0)`.

- `policy-improvement-witness`
  - Expected: `sat`
  - Recomputes every improvement round's `Q(s, a)` against the evaluated
    values, requires each round's unique greedy argmax to equal the next
    committed policy, and requires the final round to reproduce its own
    policy (termination by stability).

- `policy-monotonicity-witness`
  - Expected: `sat`
  - Checks the componentwise monotone improvement
    `(2, 2/3, 0) <= (2, 3, 0) <= (5/2, 3, 0)` with a strict improvement
    somewhere at every round, ending at the optimal values.

- `bad-policy-value-rejected`
  - Expected: `unsat`
  - Replays the first policy-evaluation linear system and rejects the
    malformed claim that `V_pi0(s2)` is `1/2`.

## Checked Evidence

- `qf-lra-bad-policy-value`
  - Expected: `unsat`
  - Source artifact:
    `artifacts/examples/math/finite-policy-iteration-v0/smt2/bad-policy-value-farkas-conflict.smt2`
  - Route: QF_LRA/Farkas
  - Regression:
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_policy_iteration_bad_policy_value_artifact_emits_checked_farkas`

## Horizon

- `general-policy-iteration-theory-lean-horizon`
  - Expected: `not-run`
  - The policy-improvement theorem in general, policy-iteration termination
    and optimality, modified/asynchronous variants, average-reward and
    continuous MDP theory, the LP formulation, Q-learning, and
    floating-point dynamic programming are not checked by this pack.
