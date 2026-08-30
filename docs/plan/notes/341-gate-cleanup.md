# Lane 341 — the 43 `check-fast` failures, per step

Detail behind [`docs/plan/status/341-gate-cleanup.md`](../status/341-gate-cleanup.md).

    before   CHECK_FAST|NOT-A-FULL-GATE|declared=404|ok=248|failed=43|deferred=113|budget=3s
    after    CHECK_FAST|NOT-A-FULL-GATE|declared=405|ok=273|failed=17|deferred=115|budget=3s

All 43 were re-run at the merged HEAD first: **all 43 still failed**, so none was
an artifact of a stale list. `declared` rises by one because this lane
registered a new control in both `scripts/check.sh` and the justfile.

An intermediate run at `failed=23` caught three steps this lane had itself
broken by regenerating. Those are fixed and described below; the final run is
the one quoted above. Deferred rises by exactly 2, the two host-conditional
steps — the intermediate 121 was timing variance in the over-3s bucket, not a
step going quiet.

## Fixed

| cause | steps | what moved |
| --- | --- | --- |
| fact DAG cycle | `autogenesis-baseline` (+2 downstream) | a spurious `depends_on` back-edge made `log_mono_right` and `log_monotone` mutually dependent; the source says only one direction is real, and the `clog` pair is the positive control |
| stale derived views | 10 regenerations | these described a 698-fact ledger; it has 2,220 facts |
| real finding | `external-coupling` (+ test) | two 40-hex CI revisions under unregistered keys; both verified to be this repo's own tested commit before registering |
| real finding | `import-status` (+ test) | README counts stale, **and** the check only ever read the first occurrence of each claim |
| real finding | `tactic-catalog-census` | crashed with `KeyError: 'revision'` on every run since 2026-08-24; ADR-0553 deleted that field |
| real finding | `kernel-facts-audit` | a hand-authored fact carried a `curation` marker defined only for generated ones |
| stale pin | `must-decline` tests | population 10 → 11, all 11 ground-truth verified, checker already passing |
| ratchet | `control-tests-reachable` tests | orphan count had fallen 16 → 15 and the baseline had not followed |
| stale pin | `holdout-isolation` tests | 67 → 116, and a comment asserting v1 was unchanged had stopped being true |
| host-conditional | 2 `binomial-arrow` steps | need the maturin-built `axeyum._native`; now `optional:`, deferred not failed |

### Self-inflicted, caught by re-running the gate

Regenerating broke two green steps. `propose-nursery-refill` fired its own R2
stale-snapshot guard (the vocabulary hash moved), fixed by the `--remeasure` it
names; `binomial-connective-ranking` needed one sha256 rebinding. Confirmed by
A/B against `accc38669` in a detached worktree rather than assumed.

## Left red deliberately

- **`autogenesis-nursery`** — three `depends_on` components each span
  *development* and *train*. **None touches held-out**, so the blind population
  is intact. The fix moves rows between partitions, which is an ADR-0542
  amendment and a methodological decision, not gate cleanup.
- **`development-partition`** — one operation authored against three
  development facts with no train fact. Same family of problem.
- **`mobility-census`** — 3 real violations, kept red by an earlier lane today
  after clearing 126 spurious ones. Unchanged here.
- **`local-ci-freshness`** — the newest record is 271 h old and 4,181 commits
  behind, and the battery has gained a step since. Only a real local-ci run
  clears it.
- **`plan-authority`** — status files total 1.98 MB against a 944 KB budget
  across 304 lanes. Systemic; `archive-plan-status.py --apply` is the tool.
- **`obstruction-graph`** (+ test) — a decline shape its predicates do not
  classify. It refuses to drop what it cannot classify, which is correct.
- **`autogenesis-mathlib-facts`** — one fact reported absent/stale/mutated.
- **`open-frontier-axiom-freeness-controls`** — 117 open non-held-out
  propositions absent from the census.
- Remaining pinned-count tests (`nursery-split`, `dispatch-baseline`,
  `theorem-production-ledger`, `production-provenance-ledger`,
  `next-reusable-family`, `correspondences`, `binomial-arrow-measurement`) —
  each needs its own check that the move was legitimate. I did the three I
  could verify and stopped rather than bump numbers to green.
