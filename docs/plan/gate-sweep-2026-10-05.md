# Gate sweep, 2026-10-05: what is red on `a38d5f5da`

Measured during the planning consolidation (PLAN.md item ENG-1). Evidence, not queue.

**Method.** Every non-cargo step of `scripts/check.sh` (445 of 556; `AXEYUM_CHECK_LIST=1`
lists them, `uv run` steps excluded) was run from a detached worktree of `a38d5f5da`,
8 at a time, 400 s cap per step, on s4 under other load. Steps that failed there were
re-run **alone, sequentially, 900 s cap** where they mattered to the consolidation.
The parallel sweep over-reports: several control scripts edit tracked files in place
while they run, so concurrent steps can see a mutated tree. Only the sequential column
is a finding.

## Red when run alone (25)

Exit status in parentheses; 124 is the timeout. Environment-dependent steps (e.g.
`carcara-gate` needs the Carcara binary) still count until shown otherwise.

- `absence-claims` (1)
- `artifact-ownership` (124)
- `artifact-ownership-tests` (1)
- `autogenesis-capability-gap-fresh` (1)
- `autogenesis-concept-coverage-fresh` (1)
- `autogenesis-mathlib-nursery-split` (1)
- `autogenesis-nursery-refill` (1)
- `autogenesis-producer-evaluation-frontier-fresh` (1)
- `carcara-gate` (1)
- `carcara-gate-self-check` (1)
- `dispatchable-frontier-statable` (1)
- `import-status` (1)
- `kernel-stack-envelope` (1)
- `ledger-coverage` (1)
- `loss-list-freshness` (1)
- `merge-hygiene` (1)
- `mobility-census` (1)
- `obstruction-graph` (1)
- `obstruction-graph-tests` (1)
- `parity-freshness` (2)
- `propose-nursery-refill` (1)
- `proposition-duplication` (1)
- `python-coverage` (1)
- `shape-duplicates` (1)
- `theorem-production-ledger` (1)

## Fixed by the consolidation (3)

`plan-authority` (the lane-count-derived ceiling, now a fixed active-lane bound),
`example-inventory-count` and `example-inventory-controls` (203 → 260 examples).

## Failed in parallel, passed alone (4)

`autogenesis-knowledge-controls`, `autogenesis-statement-adapter`, `smtcomp-resume`, `statable-vocabulary`

## Failed in parallel, not re-run alone (79)

Unknown: each is red or an interference artifact until run alone.

`admission-limit-basis` (2), `admission-limit-basis-controls` (1), `adopted-controls` (1), `aggregate-scope` (1), `artifact-gate-provenance` (1), `artifact-gate-provenance-tests` (1), `autogenesis-apply-search` (1), `autogenesis-baseline` (2), `autogenesis-concept-coverage` (1), `autogenesis-concept-coverage-content` (1), `autogenesis-fact-transaction-tests` (124), `autogenesis-factorial-zero-admission` (1), `autogenesis-induction-search` (1), `autogenesis-kernel-lemma-index-fresh` (1), `autogenesis-kernel-projection-fresh` (124), `autogenesis-nat-fib-gcd-premise-selection-policy` (1), `autogenesis-nat-fib-gcd-premise-selection-policy-tests` (1), `autogenesis-next-reusable-family` (1), `autogenesis-next-reusable-family-tests` (1), `autogenesis-nursery-dispatch-baseline` (1), `autogenesis-nursery-dispatch-baseline-tests` (1), `autogenesis-nursery-refill-tests` (1), `autogenesis-operation-execution-tests` (124), `autogenesis-proposer-isolation` (1), `autogenesis-statement-reflexivity` (1), `autogenesis-statement-reflexivity-admission` (1), `autogenesis-transport-projection-fresh` (1), `constant-canonicity` (124), `constant-canonicity-tests` (1), `control-tests-reachable` (1), `control-tests-reachable-controls` (1), `correspondences-tests` (1), `curriculum-bucket-cohesion` (124), `deep-stack-call-sites` (1), `deep-stack-call-sites-controls` (1), `dispatchable-frontier-tests` (1), `episode-tests` (1), `external-coupling` (1), `external-coupling-tests` (1), `fact-derived-numbers` (1), `fact-derived-numbers-tests` (1), `fact-frontier-tests` (124), `facts-replay` (124), `gate-controls` (1), `gate-liveness` (124), `graph-dispatcher-gen` (1), `graph-dispatcher-tests` (1), `graph-join` (1), `import-status-tests` (1), `kernel-facts-audit` (1), `kernel-stack-envelope-controls` (124), `lane-turn-controls` (124), `local-ci-freshness` (1), `lra-hypothesis-binding` (124), `open-frontier-axiom-freeness-controls` (1), `optional:py-cindergraph-defects` (2), `optional:py-cindergraph-defects-tests` (1), `parity-ancestry` (2), `parity-ancestry-controls` (1), `parity-freshness-controls` (1), `prelude-reuse` (124), `product-health` (1), `production-provenance-ledger-tests` (1), `propose-nursery-refill-tests` (1), `python-controls` (1), `python-coverage-tests` (1), `safety-matrix` (1), `shell-antipatterns` (1), `shell-antipatterns-controls` (1), `smt-evidence` (124), `solver-module-graph` (1), `solver-module-graph-tests` (1), `spivak-cas-column` (1), `spivak-cas-column-tests` (1), `test` (124), `theorem-inventory-completeness` (124), `theorem-production-ledger-tests` (1), `trust-closure` (124), `trust-closure-controls` (124)

## Gates the sweep did not cover: `just check` only

`scripts/check.sh` and `just check` differ (`scripts/check-aggregate-scope.sh`).
`check-parity-docs.py` runs only under `just check` and was red on `a38d5f5da`
with 111 errors. After this consolidation it has 104, none new (diffed line by
line against `a38d5f5da`): 92 Cargo examples missing from
`docs/reference/examples.md`, 6 stale parity rows and a division count in
`docs/PROJECT-STATE.md` (now a historical summary — decide whether the gate
should still read it), and 6 boundary markers missing from
`docs/internals/*.md`, `crates/axeyum-cnf/src/lrat.rs`,
`crates/axeyum-ir/src/sort.rs` and one contributor guide.

The whole `just parity-docs` recipe (87 commands) was also run alone on both
trees: 23 commands fail on `a38d5f5da` and the same 23 fail after this work —
mostly Lean U2/execution-evidence generators whose `--check` output has drifted,
plus `gen-scoreboard.py --check` and `check-import-status.py`.
