# Lane: nra-admission-bound — the NRA cross-product admission bound

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nra-admission-bound, 2026-09-07).**

**Task.** The QF_NRA loss census
(`bench-results/parity-losses-20260906/QF_NRA.census.tsv`) attributed 62 of 77
reference-only losses (80.5%) to one cause: `nra.rs`'s deterministic
cross-product admission bound of 2 — the largest single named cause on the
parity board. Establish **what the bound protects** before changing it, then
raise or replace it with a measured budget, or report that it is correct and
the 62 files need a different route.

## What the bound protects, established

It was introduced by `9a8b09220` (2026-06-19) as an **OOM guard**. Two things
were settled before touching it:

- **Not soundness, and not from the comment.** Admission gates *reachability*:
  the abstraction is a relaxation (only `unsat` transfers) and every `sat` is
  replayed against the original assertions by the ground evaluator in
  `check_with_nra`'s outer guard. Both arguments are independent of the count,
  so opening the bound cannot produce a wrong verdict — only cost memory or
  time.
- **Not memory, measured.** 62 files, one binary, arms differing only in an env
  override, 24 s / 8 GiB, `taskset -c 0-7`, arms interleaved, idle s6:
  **zero memory aborts in 124 runs**, peak RSS **3,315 vs 3,316 MiB** against an
  8 GiB cap. It protects **wall time**. And on **25 of the 62 it protects
  nothing at all** — those files are refused one layer down by
  `lra_theory::MAX_ONLINE_LRA_ATOMS` in the same time and the same memory, so
  the census's dominant class named the first gate in a chain rather than the
  one that refused.

The producer metered in cross-products (2) while the consumer meters in distinct
linear-real atoms and refuses above 1,024 — 15× apart, in different units. The
ratio between them is not a constant either (13.1–30.3 atoms per cross-product
across four census files), so the count cannot simply be rescaled.

## The slice

[ADR-1751](../../research/09-decisions/adr-1751-nra-admission-is-the-consumers-capacity.md):
admission is the consuming engine's atom capacity, counted rather than
converted. At or below the legacy line of 2 the path is byte-identical; above it
the existing cheap refutations still run first (so nothing decided today can
regress) and the relaxation gets half the remaining deadline, because `unknown`
is a fall-through for the QF_NIA and UF+NRA callers.

## Result, on the committed 200-file list

One binary `c2d7635815d5` (different from the diagnostic binary by sha256),
arms interleaved, s6.

| | legacy | shipped default |
|---|---:|---:|
| decided | **110/200** | **112/200** |
| verdict regressions | — | **0** |
| disagreements | — | **0** |
| memory aborts in 400 runs | 0 | **0** |
| total wall | 1,006 s | 1,374 s |

The legacy arm reproduces this division's recorded ledger row exactly (110/200),
which is what makes 112 comparable. Both new results are `sat`, both agree with
cvc5 run directly on the same host, both declared `:status unknown` in the file,
and both carry `evidence kind=sat-model certified=1`.

**Honest remainder:** 60 of the 62 census files are still lost, and they are now
a **capability** gap rather than an admission-policy one — 35 admitted and not
closed by the linear-abstraction relaxation, 25 refused by the atom capacity.
`MAX_ONLINE_LRA_ATOMS` is the next bound on this route; its own doc records that
lifting it needs the atom-normalization memory addressed first.

**Not done:** QF_NIA was not re-measured. The deadline share exists to protect
that fall-through caller and is argued from the structure plus the measured
times-to-decide, not from a QF_NIA sweep.

## Gates

`check --workspace --all-targets --all-features` ok; `clippy --workspace
--all-targets --all-features -D warnings` ok; `-p axeyum-solver --lib --features
full` 1,475 passed; `--test corpus_regression` 1; `--test nra` 37; `nra_real_root`
86, `nra_no_hang` 3, `nra_census_levers` 8, `cas_ideal_route` 36;
`--features z3`: `qf_lra_differential_fuzz` 5, `simplex_lra_fallback_differential`
1, `qf_uflra_differential_fuzz` 1, `nra_differential_fuzz` 3,
`qf_ufnra_differential_fuzz` 1, `nia_differential_fuzz` 1;
`progress_frontier --features full -- --test-threads=1` 12, no REGRESSION.
Every count read off the run.

**Mutation control:** `if !admitted {` → `if false && !admitted {` in a scratch
copy killed **exactly one** test
(`a_chain_past_the_consumer_capacity_declines_naming_atoms_not_a_count`), 36
passed; source restored and re-verified.

Raw per-file data for both sweeps is committed beside the census
(`bench-results/parity-losses-20260906/QF_NRA.admission-ab62.tsv` and
`…-ab200.tsv`); `exit` is a column, not an inference, and it is `0` on all 524
runs. Full record:
[`docs/research/12-performance/nra-admission-bound-2026-09-07.md`](../../research/12-performance/nra-admission-bound-2026-09-07.md).

**`gen-plan.py --check` is red on this branch, by instruction.** The lane brief
forbids running the generator or editing `PLAN.md`; the only drift is this
lane's own block (104 added lines, 0 removed, verified by regenerating into a
scratch copy and restoring). Folding it in is the coordinator's step.

## Landed changes

| when | what | commit |
|---|---|---|
| 2026-09-07 | Lane opened: archaeology of what the admission bound protects, and the measurement plan fixed before the data | `d2d45394f` |
| 2026-09-07 | An env A/B lever so the bound could be measured rather than argued about | `41e5ff267` |
| 2026-09-07 | The measurement: the bound is not the binding gate — lifting it hands the query to the LRA atom cap, same time, same memory | `ad77e3f55` |
| 2026-09-07 | Admission is the consuming engine's capacity, not a cross-product count (ADR-1751) | `07b8da6ca` |
| 2026-09-07 | ADR-1751, the Q2/Q3 measurements, and three admission tests incl. the mutation-checked gate guard | `a322d1149` |
| 2026-09-07 | Backtick logic names in the new doc comments (workspace clippy) | `f27b1dbd1` |
| 2026-09-07 | The 200-file confirming run, the census correction block, the family-doc follow-up, and the capability entry's measured boundary | `0857e419c` |
| 2026-09-07 | Merge of local `main` (ADR index regenerated to resolve); post-merge workspace `check` and `clippy -D warnings` both green | `1c078316b` |
