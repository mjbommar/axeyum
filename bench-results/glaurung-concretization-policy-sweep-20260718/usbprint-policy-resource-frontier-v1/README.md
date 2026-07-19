# Usbprint scalar-policy resource frontier v1

ADR-0249's exact execution is preserved here as a **rejected** result. It ran
from clean detached Axeyum
`f951152517a6bdcf0410d88c48c2cc3a167cac6a` against clean isolated Glaurung
`7f682e5`. Fourteen of 15 cells completed, all five policies established a
common prefix of 10, and four policies completed prefix 15. The final
prefix-15/site-hash-one cell failed exact work reproduction, so the aggregate
correctly records no resource bracket.

## Cell summary

Every accepted cell reproduced its raw diagnostic set, zero high-confidence
findings, solve count, and policy telemetry across two Z3 and two Axeyum runs.
Solve counts below are per authority/repetition.

| Prefix | Policy | Result | Raw diagnostics | Solves |
|---:|---|---|---:|---:|
| 5 | AnyModel | accepted | 31 | 2,884 |
| 5 | min-unsigned | accepted | 39 | 208,110 |
| 5 | max-unsigned | accepted | 22 | 49,704 |
| 5 | site-hash-0 | accepted | 26 | 111,326 |
| 5 | site-hash-1 | accepted | 35 | 211,152 |
| 10 | AnyModel | accepted | 89 | 7,531 |
| 10 | min-unsigned | accepted | 94 | 379,298 |
| 10 | max-unsigned | accepted | 42 | 88,224 |
| 10 | site-hash-0 | accepted | 81 | 250,153 |
| 10 | site-hash-1 | accepted | 56 | 281,372 |
| 15 | AnyModel | accepted | 146 | 14,626 |
| 15 | min-unsigned | accepted | 140 | 638,349 |
| 15 | max-unsigned | accepted | 65 | 156,228 |
| 15 | site-hash-0 | accepted | 114 | 320,485 |
| 15 | site-hash-1 | rejected | 91 | Z3 541,685; Axeyum 522,032 / 522,296 |

The rejected cell emitted the same 91 raw diagnostics and zero high-confidence
findings in all four runs. Z3 work was stable at 541,685 solves, 8,257
canonical attempts, 8,120 completed choices, 137 infeasible choices, and
536,057 probes. Axeyum drifted between:

- 522,032 solves, 7,951 attempts, 7,825 completed choices, 126 infeasible
  choices, and 516,576 probes; and
- 522,296 solves, 7,955 attempts, 7,829 completed choices, 126 infeasible
  choices, and 516,840 probes.

That outcome is neither exact fixed work nor ADR-0249's preregistered four-run
resource-bound classification. The aggregate therefore has
`accepted=false`, `matrix_complete=false`, common completed prefix 10, and
`first_resource_bound=null`.

## Post-result attribution

Glaurung `7f682e5` exposed the outer analyzed-function count but not the reason
each inner symbolic worklist stopped. A post-result-only instrumentation
candidate on isolated branch `axeyum-concretization-policy-a0` at `ff3c0a7`
added explicit stop classes. An otherwise identical diagnostic Axeyum run
retained the 91/0 raw/high output and reported:

```text
[canonical-model-choice] policy=glaurung-site-hash-1-v1 attempts=7957 completed=7831 infeasible=126 probes=516972 inconclusive=0 error=0 unsupported_width=0 no_solver=0 unknown=0 final_unsat=0
[exploration-limits] runs=40 completed=36 state_budget=3 solve_budget=0 timeout_budget=0 deadline=1
[solver] backend=axeyum solves=522428 solver_time=903801.9ms avg=1730.0us check_timeout_ms=250
```

One deadline-terminated inner worklist explains why repeated canonical work
drifted even though both runs said they analyzed 15 functions. Each additional
canonical attempt contributes 66 probes/solves here, matching the observed
increments. This diagnostic is attribution only: it does not enter or
rehabilitate the preregistered result.

Future fixed-work evidence must require the exploration-stop partition and
reject any deadline- or timeout-terminated worklist. These artifacts make no
solver-speed, recall, complete-driver-equivalence, symbolic-memory, or default-
policy claim.

## Exact identities

- preregistration SHA-256:
  `dc7be000b2f38216011dc31b465c6abccf57d2d9a35ed185289e7f72c7a280c8`
- execution manifest SHA-256:
  `1d44f623d8a7ba97e7424d07f278a072d570503a3a71f01c8c078b640cfe23a2`
- rejected analysis SHA-256:
  `848a7448831755c96c69fb6eb030682e30a6fba30b4aa7edd59c5db1764a849f`
- rejected prefix-15/site-hash-one report SHA-256:
  `97acdffc778a58cd5bf8d51a55164848f4b746d92b749bcdfb3d5d88239a876a`
- retained failing stderr SHA-256:
  `0231d36316a15965c476bf81df07e1cfb9b6406c9685131b56dc876ca91439eb`
