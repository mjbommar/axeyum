# Finite Linear Discriminant Checks

This pack is for learners, statistics users, linear-algebra contributors, and
proof-route contributors who need a tiny exact Fisher-style discriminant
example. It checks one two-class rational sample and keeps finite training-set
arithmetic separate from statistical classification theory.

The pack covers:

- exact class means for two finite two-dimensional classes;
- centered rows and within-class scatter matrices;
- a fixed Fisher direction solving `S_w w = mu_1 - mu_0`;
- finite projected scores and midpoint-threshold replay;
- rejection of a malformed discriminant direction;
- a source-linked QF_LRA/Farkas row for the final bad-direction conflict.

The core trust boundary is:

```text
untrusted fast search -> discriminant direction, finite scores, or Farkas certificate
trusted small checking -> exact rational replay and rechecked QF_LRA/Farkas evidence
```

This is not a theorem about all Fisher linear discriminants, Gaussian class
models, Bayes-optimal classifiers, statistical generalization, regularized LDA,
floating-point covariance estimates, or production classification pipelines.
Those stay in the Lean/numerical-honesty horizon.

## Rows

| Row | Result | Trust |
|---|---|---|
| `class-mean-witness` | `sat` | replay-only |
| `within-scatter-witness` | `sat` | replay-only |
| `fisher-direction-witness` | `sat` | replay-only |
| `finite-threshold-classification-witness` | `sat` | replay-only |
| `bad-fisher-direction-rejected` | `unsat` | replay-only |
| `qf-lra-bad-fisher-direction` | `unsat` | checked QF_LRA/Farkas |
| `general-linear-discriminant-theory-lean-horizon` | `not-run` | lean-horizon |

Validate the pack with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-linear-discriminant-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_linear_discriminant_bad_direction_artifact_emits_checked_farkas
```
