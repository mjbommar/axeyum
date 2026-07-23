# SMT-COMP credited full-population publication fixture

Status: process-free implementation integrated by `origin/main` merges
`f65f4647` and `c4d9050a`; live F2 preparation, execution, and comparison remain
outstanding

Date: 2026-07-23

Plan: [credited full-population execution](smtcomp-credited-full-population-plan-2026-07-23.md)

## Result

The credited lane now has the missing process-free publication boundary for a
completed solver cell and for the final same-population comparison. This work
used only temporary synthetic records. It did not probe a host, run a sentinel
or solver, create an allocation or resource session, or read or mutate a live
NAS run root.

One cell result now publishes, in order:

1. a sealed execution authority binding the preparation, selection, run, plan,
   schedule, ordered wave-checkpoint seals, resource completion, multi-host
   completion, population, key set, record set, and completion timestamp;
2. canonical sequence-ordered result records;
3. an overall and per-logic adjudication; and
4. `complete.json` last.

Live authority accepts only all 45,905 v2 result records and all 16 checkpoint
seals. A known-status contradiction is retained in the external result with
`safe_to_continue=false`; it cannot become comparison authority or admit the
next solver.

The comparison loader validates all three external result roots itself. It
requires identical preparation, selection, population, fixture scope, and safe
completion. The final comparison derives:

- native reported-status, decision-class, and typed-termination counts overall
  and for every logic;
- all three pairwise decide/decline/disagreement projections overall and per
  logic; and
- three-solver three/two/one/none/disagreement projections overall and per
  logic, including sole-decider and sole-non-decider counts.

Every cell must contain the identical benchmark key set and the exact sequence
range. Known-status contradictions and cross-solver `sat`/`unsat`
disagreements block comparison publication. The comparison keeps official
SMT-COMP, performance-ranking, and single-scalar-ranking claims false and
installs its own `complete.json` last.

## Mutation and interruption boundary

The eleven focused tests reject:

- same-sized benchmark replacement, duplicate keys, sequence gaps, and shared
  expected-status drift;
- malformed live result schemas, resealed summary changes, known-status
  contradictions, and cross-solver disagreements;
- cell-result record mutation, extra prepublication files, incomplete or
  unsafe cell authority, and mutated comparison bytes; and
- any artifact added to either completed namespace.

Interrupted cell-result and comparison publications retain no completion. A
retry with the same authority reproduces identical already-installed bytes and
then installs completion last.

## Gates

```text
python3 -m unittest \
  scripts.tests.test_smtcomp_full_compare \
  scripts.tests.test_smtcomp_full_result
11 tests, OK

./scripts/check-smtcomp-resume.sh
126 tests, OK (one expected live-host skip)
runner/scoring/pipeline/selection/provenance checks, OK
generated resume contract, selection authority, and repaired-P0 comparison, OK
```

The branch-wide gate remains red at the previously recorded out-of-lane
bench/CAS formatting drift. This increment did not edit those files.

## Remaining execution boundary

This fixture does not make F2, F3, or F4 complete. Before a real cell result can
publish, the F3 coordinator still must validate the exact live preparation,
all 16 checkpoint records and underlying allocation terminals, the final
resource and multi-host completions, every v2 record and output sidecar, and the
45,905-row selection. Only then may it construct the execution authority
consumed here. The complete three-cell comparison remains impossible until all
three sequential cells have safe external results.

These source/result bytes are integrated. No live action is authorized until
the exact current `origin/main` passes both readiness gates and an exact F2
result is integrated by the mainline owner.
