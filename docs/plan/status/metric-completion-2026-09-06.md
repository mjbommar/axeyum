# Lane `metric-completion` — 2026-09-06

Topic 4, carrier 1: the metric completion. ADR number **1678**.

## Status

The **measurement landed first and it moved the sizing** (ADR-1678). The
construction's carrier layer landed behind it as `metric_completion.rs`, a new
top-level module on the `metric_prod.rs` pattern — nothing in `metric.rs`,
`metric/` or `metric_prod.rs` was edited, so no other lane's file was touched
and the `Metric` prelude's build cost did not move.

### What the re-measurement found

ADR-1625 sized a generic completion at "four new lemmas about `CReal.limit`,
proved from `CReal.limit_dist` and nothing else", over a carrier
`Subtype (Nat -> M.carrier) (Metric.Regular M)`. Both halves are wrong in ways
that make the task smaller, not larger.

| ADR-1625 said | measured 2026-09-06 |
| --- | --- |
| carrier predicate `Metric.Regular` | does not exist; all eight `Regular` tokens in `metric.rs` are `ReducibilityHint::Regular(1)`. Does not need to: `Metric.CauchyAt M f 1` IS Bishop regularity |
| four new lemmas about `CReal.limit` | zero of them is on the critical path: `CReal.limit` is the superseded term former, and `converges_of_scaled_cauchy` NAMES the limit, so all four are `converges_unique`/`converges_le`/`converges_add`/`converges_lower_bound` verbatim |
| plus a speedup bridge | `CReal.regular_of_scaled_cauchy`, shipped and exact |
| "1 of 33 reusable" | inverted inference. `Metric.dist` is `CReal`-valued, so the completion's distance IS a `Nat -> CReal` sequence: 33 of 33 instantiate, 14 of 33 are consumed |
| `33` not re-derivable (reviewer 02) | re-derivable: live `add_declaration` sites outside `#[cfg(test)]` modules. Naive 36; the three extras are `converges_le_tests`'s own mutation probes |
| — | new-mathematics budget is **one** estimate: `Metric.dist_diff_le`, the four-point reverse triangle inequality |

One correction to the brief's own count: `Metric.Complete` has **two**
witnesses (`Metric.creal_complete`, `Metric.prod_complete`).
`Metric.creal_completeOn_interval` witnesses `Metric.CompleteOn`, a different
predicate.

### What landed in the kernel

`crates/axeyum-lean-kernel/src/metric_completion.rs`, 11 declarations, zero
axioms:

- `Metric.RegularSeq`, `Metric.regularSeq_cauchyAt`, `Metric.regularSeq_bound`
- `Metric.CompletionSeq`, `Metric.completionSeq_carrier`
- `Metric.completionVal`, `Metric.completionRegular`
- `Metric.completionDistSeq`, `Metric.completionDistSeq_eval`
- `Metric.embedSeq`, `Metric.embedSeq_val`

The accounting test derives its subject by **differencing two kernels** (one
with `build_metric_prelude` alone, one with `build_metric_completion_prelude`)
rather than by a name-prefix filter — the gap ADR-1625 recorded for
`Metric.*` names declared outside `metric.rs`.

## Next

1. `Metric.dist_diff_le` — the one new estimate.
2. `Metric.completionDist` via `CReal.mk (speedup (diagonal D) K)`, then the
   twelve field witnesses with `equiv := dist ~ 0`.
3. `Metric.Complete (Metric.completion M)`, then `RN.metric n` (58 `RN`
   declarations wait on it).
