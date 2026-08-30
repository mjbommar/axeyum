# 382 — L0/S0: the safety matrix census

<!-- plan-section: lane-status -->

Lane: `l0-safety-matrix`
Phase: ADR-0717 L0, roadmap phase **S0** — complete.
Decision: [ADR-0746](../../research/09-decisions/adr-0746-the-safety-matrix-is-generated-and-gated.md)

## Status

S0's exit criterion is met and gated. `scripts/gen-safety-matrix.py` generates
`artifacts/safety-matrix/safety-matrix.tsv` (one row per proved fact, exactly
once) and `safety-matrix-summary.md`; `--check` runs in both `scripts/check.sh`
and the justfile, and `check-aggregate-scope.sh` still reports its recorded 64
divergences, so the registration is two-sided.

Six mutations, three distinct guards, each firing through the right one —
deleting a controlled fact, dropping its checker, unsettling it, deleting an
**uncontrolled** fact, downgrading an own-subject checker to the shared prelude
sweep, and breaking a classifier so it matches nothing. Full table in ADR-0746.

**No fact was edited.** This lane is measurement only.

## The numbers a later phase should start from

2,270 facts, 2,117 `proved`. Median protections per fact: 3.

| protection | facts / 2117 |
|---|---:|
| `env_footprint` (prelude-wide sweep) | 1859 |
| `kernel_theorem` (explicit binding) | 1466 |
| `coverage_bearing_checker` (own subject) | 1442 |
| `exact_statement` (drift pin) | 142 |
| `semantic_falsification` | 91 |
| `per_theorem_footprint` | 59 |
| `circularity` | 38 |
| `mutation_control` | 14 |
| `independent_replay` | 8 |

53 facts hold none of the nine. 523 hold one, and for 400 of those the one is
the prelude sweep.

Checker fan-out: 2,284 distinct commands, **largest 463**
(`--require-axiom-free creal`), then 318 and 280. 2,221 commands serve exactly
one fact; only 48 proved facts have no checker of their own and 17 cite none.

## Three findings that should change how a later phase is scoped

1. **The evidence `kind` enum no longer discriminates.** 1,901 rows declare
   `exhaustive-enumeration` or `instance-pin` while their `supports` records an
   axiom footprint. Reading `kind` at face value turns a true semantic-
   falsification count of 91 into 1,992. S3 must not size itself off `kind`.

2. **The statement-drift gate covers 6.8% of settled facts and exits 0.**
   `check-settled-fact-statements.py` reports `settled=2119|pinned=144`; a fact
   absent from the manifest is treated as newly settled, never as a gap. S1's
   first move is a coverage assertion on that manifest, not new machinery.

Detail moved to [`../notes/382-l0-safety-matrix.md`](../notes/382-l0-safety-matrix.md).

