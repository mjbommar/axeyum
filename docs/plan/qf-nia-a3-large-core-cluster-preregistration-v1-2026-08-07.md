# QF_NIA A3 large-core cluster preregistration v1 — 2026-08-07

## Selection boundary

Baseline is clean integrated
`bd413357cd967aed0f2f5a1281ca0a6a8f9a276b`. The complete population remains
bound by causal-census SHA-256
`2585b9627fb851b06428455eb1e0754e01083c0cb17b2c24c6404087c105203a`
and retained-sidecar SHA-256
`392e6cc33423518a44015a98cb1c7fdf867ea1c33ffd1cb77f761316acb5d524`.
The later exact 13-row production capture used for this partition has SHA-256
`c0692db87ac1050f5eb29c06202ae158c9f34e06857f2f14feb9cf5868fbd558`.

The rejected probe-model population left five reference-SAT rows in arithmetic
DPLL/core search. Existing route counters separate a repeated-large-core pair:

- `SAT14/1051.smt2`: 203 completed support probes, 180 `Large` cores,
  average core length 455.0, maximum 653, then a warm propositional-SAT timeout;
- `SAT14/1280.smt2`: 437 completed support probes, 409 `Large` cores,
  average core length 317.5, maximum 490, then the query-global lazy-loop
  timeout.

The exact ordered target list is
[`large-core-v1-targets.txt`](evidence/qf-nia-a3/large-core-v1-targets.txt),
SHA-256
`09d46491340903af0181bde3cf8f08af073268b1b62bc937349d4eab5aecde17`.

Three other reference-SAT rows are routing controls, not score targets for this
cluster:

- `p4943` and load-sensitive `p1784` are small-core dominated, with zero
  recorded `Large` cores;
- `p32598` emitted one terminal 4,679-literal `Large` core but is not repeatedly
  large-core dominated.

Their ordered list is
[`large-core-v1-routing-controls.txt`](evidence/qf-nia-a3/large-core-v1-routing-controls.txt),
SHA-256
`df0e044140a72a4e8fa0eb733745e9d7b91e2f6b014b586fb0302ee34403a05b`.

## Diagnostic hypothesis

`theory_conflicts_for_indices` records `ArithCoreSource::Large` for two
different reasons: the exact inconsistent index set exceeds the 128-atom
deletion-minimization admission guard, or the query deadline has already
passed. Both are sound—the full inconsistent set is a valid core—but they imply
different next work. Repeated oversized cores create hundreds of broad blocking
clauses and may dominate the warm SAT skeleton; deadline-only large cores are a
secondary symptom and do not authorize a core algorithm change.

The first increment is diagnostic-only. Add bounded deterministic aggregate
statistics that split `Large` by admission-size versus deadline, record core
length count/min/max and fixed histogram buckets, and distinguish whether the
terminal stop occurs in the theory oracle, core extraction, or warm SAT solver.
Do not record source terms, literal identities, models, or elapsed-time-derived
policy. Do not change the 128-atom guard, minimize a core, alter a learned
clause, reset a deadline, or change route order.

No implementation is authorized until both targets reproduce repeated
size-admission `Large` cores and the same actionable downstream mechanism in at
least two of three direct observations each. If either row is deadline-only,
fails to reproduce, or differs causally, reject or repartition the cluster.

## Targets and controls

Both targets are declared/reference SAT and current Axeyum `unknown`. A future
gain counts only when Axeyum returns SAT and the model replays every selected
literal and original assertion.

Mandatory controls are:

- the three routing controls above;
- the six reference-UNSAT rows in
  [`reconstruction-deadline-v1-controls.txt`](evidence/qf-nia-a3/reconstruction-deadline-v1-controls.txt),
  SHA-256
  `cf8d03e83b237aeea2413bf23b317b590429c40f08e0d955e8b50824212014e3`;
- the 34 retained QF_NIA decisions in the bound sidecar;
- the ADR-0378 giant-`distinct` process-survival row;
- existing small-core, model-replay, typed-decline, and opaque-UF unit controls.

## Gates and stop conditions

1. Diagnostic instrumentation must preserve every target/control verdict under
   the existing 8 GiB and 24,000 ms protocol.
2. Direct target observations must reproduce repeated size-admission large
   cores in at least two of three runs per row before mechanism selection.
3. Any core-search change requires a second preregistration naming its exact
   deterministic work bound, target/control outcomes, and removal rule.
4. A two-row A/B is the first implementation gate. At least one target must
   become replay-checked SAT and every control remain sound before a fresh
   200-row run is authorized.
5. Retain code only if all 34 prior decisions remain identical, every new SAT
   model replays, no disagreement appears, and the existing memory/deadline
   protocol remains intact.

Stop on any wrong SAT, replay failure, reference-UNSAT-to-SAT change,
prior-decision loss, memory ceiling, general cap increase, new or reset
deadline, route-order change, fixture-specific path behavior, or evidence that
the two targets do not share one stable mechanism.
