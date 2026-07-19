# Glaurung direct-root parity-leaf memo — 2026-07-19

Status: structurally accepted, rejected by the preregistered performance gate;
candidate removed

ADR-0277 preregistered one encoder-local memo for repeated visits to the same
positive direct-root parity leaf. Candidate `9533c508` and checkpoint
`900f6997` were committed before corpus observation. The production code was
removed at `4fc45767` after timing rejection.

## Structural gate

The clean detached artifact-v37 candidate run preserves all 162 decisions
(88 SAT / 74 UNSAT), manifest and in-process Z3 agreement, all 88 original-
model replays, every per-query AIG/CNF/emitted-clause shape, and every
nonselected duplicate-origin row.

Every predeclared delta is exact:

| Counter | Delta |
|---|---:|
| Clause attempts | -107,000 |
| Exact duplicates | -107,000 |
| Declared/visited literals | -321,000 |
| False constants dropped | -107,000 |
| Canonical attempted literals | -214,000 |
| Canonical binary attempts | -107,000 |
| Primary occupied/exact hits | -107,000 |
| Emitted clauses | 0 |

Parity overlap becomes zero and total residual duplicate clauses become
12,260. Register-slice contributes 23,828 removed duplicates and slice-partial
83,172; every other family changes by zero.

Retained structural files:

- [`artifact.json`](artifact.json), SHA-256
  `14b42944bf9ab8b34dad5db86b15eb8e29118739966b6cc97abedc57ddfc60ee`;
- [`analysis.json`](analysis.json), SHA-256
  `7183023780327ebb1454e2363ee948fb4f018f4812a2d143352cdd49051b91bd`.

## Unprofiled performance gate

Distinct prebuilt executables were run in the fixed order
`B,C,C,B,B,C,C,B,B,C,C,B`. Their SHA-256 identities were:

- baseline `6ff05905`: `c33065e4...bffc4`;
- candidate `900f6997`: `dcc25e24...75c6e`.

All 12 processes preserve the complete correctness and per-query structural
gates. The six paired candidate/baseline total-time ratios are:

`0.92203, 0.94796, 1.01559, 0.93189, 0.98175, 0.96439`.

The aggregate signal passes its two speed thresholds: geometric mean
`0.96009` and exhaustive deterministic bootstrap 95% upper bound `0.98146`.
The candidate is nevertheless rejected because three independent registered
guards fail:

- baseline total-time CV is 3.4250% (limit 3%);
- candidate total-time CV is 3.0152% (limit 3%); and
- mixed/trivial family geomeans are 1.04918 and 1.32691 (limit 1.02).

The retained [`timing-analysis.json`](timing-analysis.json) has SHA-256
`7a68f69684da3f651e1fbffac0cb26b911827d94dc0c717459100bacbc844816`.
The twelve source artifacts remain under [`timing/`](timing/).

## Decision and limits

The 4.0% aggregate point estimate is not promoted because the experiment
failed its variance and family nonregression gates. The trivial family contains
negligible absolute work, but that was known when the unconditional family gate
was preregistered and is not reinterpreted after observation. Do not rerun to
fish for lower variance, weaken the family rule, or claim a production speedup.

This closes the ADR-0259--0277 duplicate-clause lane on the fixed population.
The profile remains useful evidence, while production encoding returns to the
pre-candidate behavior. GQ5 may reopen only from a new independently motivated
mechanism and population, not another partition of these 107,000 clauses.
