# Finite BDF2 Method Checks

This pack records one exact rational two-step BDF2 trace for `y' = -y`.
It keeps the finite implicit multistep replay separate from general BDF2
order, stability, convergence, variable-step, floating-point, and PDE claims.

Run it from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-bdf2-method-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_bdf2_bad_step_artifact_emits_checked_farkas
```

Rows:

- `bdf2-history-witness` replays the starter value, history states, endpoint
  derivatives, and BDF2 residuals over exact rationals.
- `bdf2-monotone-decay-witness` checks only the listed finite monotone decay
  trace.
- `bad-bdf2-step-rejected` rejects a malformed finite next-state claim by
  exact replay.
- `qf-lra-bad-bdf2-step` routes the scalar contradiction through checked
  QF_LRA/Farkas evidence.
- `general-bdf2-theory-lean-horizon` marks the missing theorem route.

Trust boundary:

```text
untrusted fast search -> BDF2 trace, implicit multistep update, or Farkas certificate
trusted small checking -> exact rational replay plus checked QF_LRA evidence
```
