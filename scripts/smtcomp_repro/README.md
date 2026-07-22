# SMT-COMP scoring reproduction (in-tree replica)

A from-scratch local replica of the **SMT-COMP selection and scoring rules**,
plus a bounded self-contained execution approximation, built to measure axeyum
without touching or PR-ing the public SMT-COMP repositories. The official 2026
execution layer is BenchExec; this directory does not inherit BenchExec's
resource isolation or artifact guarantees. The upstream
tooling (`SMT-COMP/smt-comp.github.io`, `scrambler`, `trace-executor`,
`benchexec`) is read as a reference only; nothing here is pushed upstream.

Specification source: **SMT-COMP 2026 Rules and Procedures** (21st competition,
revised 2026-04-11), §5 (execution), §6 (benchmark selection), §7 (scoring).
Section references in the code point at that document.

## The pipeline, stage by stage

| Stage | Rules § | Module | Status |
|---|---|---|---|
| A. Legacy candidate selection (local cap/family approximation) | §6 | `selection.py` | **superseded for official-selection claims** |
| A′. Official Single Query selection identity | §6 | `official_selection.py`, ADR-0356 | **S0--S2 complete; S3 pinned producer next** |
| B. Resource-limited execution (wall `T`, CPU `mT`, mem; measures `aw`,`ac`) | §5 | `runner.py` | **done** (self-contained; BenchExec optional) |
| C. Result → benchmark score tuple ⟨e,n,aw,w,ac,c⟩ (all 5 tracks) | §7.1 | `scoring.py` | **done** |
| C′. Sequential benchmark score ⟨e_S,n_S,c_S⟩ (virtual CPU limit = T) | §7.1.1 | `scoring.py` | **done** |
| D. Division scoring: parallel, PAR-2, sequential, 24s, sat, unsat; disagreement removal | §7.2 | `scoring.py` | **done** |
| E. Competition-wide: Best Overall, Biggest Lead, Largest Contribution | §7.3 | `scoring.py` | **done** |
| —. End-to-end driver + local shard execution | — | `compete.py`, `run_repro.sh` | **bounded slice** |
| —. Resumable distributed execution | — | `resume_contract.py`, `resume_fs.py`, `resume_runner.py`, `resource_enforcement.py`, ADR-0344 | **E0-E3 complete** |
| —. Source-family + exact-content provenance | — | `provenance.py` | **done** |

Legacy scoring/selection tests (43): `tests/test_scoring.py` (30, one per rule),
`tests/test_pipeline.py` (6, full aggregation/ranking plus duplicate rejection),
`tests/test_selection.py` (5, §6 caps + sampling), and
`tests/test_provenance.py` (2, family normalization + exact duplicates).
Fourteen ADR-0356 tests separately validate the pinned 29-source/51-submission/
90-archive authority, complete synthetic eligibility/decision partition, all
four cap regions, the inclusive 1.0-second boundary, incoherence and
single-solver-year handling, exact fixture bytes, and rejecting mutations. The
legacy sampler never substitutes for the pinned official Polars producer.
They also parse a real-shaped `defs.py` division table and official compressed
benchmark/result/submission documents without importing organizer code.
The selection-free live runner, `scripts/audit-smtcomp-selection-inputs.py`,
also streams the full gzip inputs with bounded historical state and cannot emit
an official sample. Its completed S1b result is recorded in
[`smtcomp-official-selection-input-audit-s1b-2026-07-22.md`](../../docs/plan/smtcomp-official-selection-input-audit-s1b-2026-07-22.md).
Three S2 extraction tests reject traversal, cross-logic members, links, and
unexpected corpus roots. The resumable full acquisition entry point is
`scripts/acquire-smtcomp-selection-corpus.py`; it verifies published size/MD5,
adds local SHA-256, extracts regular files only, and writes completion last.
The completed full acquisition and fresh all-file rehash are recorded in
[`smtcomp-official-selection-corpus-s2-2026-07-22.md`](../../docs/plan/smtcomp-official-selection-corpus-s2-2026-07-22.md).
The S3 entry point, `scripts/produce-smtcomp-official-selection.py`, copies and
rehashes the exact 88-file organizer bundle twice, derives a hash-required
14-package runtime closure from the pinned Poetry lock, executes the pinned
cache-builder AST and official Polars sampler in two fresh one-thread venvs,
and rejects any normalized selection or per-logic repetition drift.
Six additional generator tests exercise the active v2 18-invariant/28-scenario
resume contract. V2 preserves observed timeout responses, uses typed process
outcomes, and attributes each record to an attempt.
Four E1a filesystem tests add real child `SIGKILL` controls at four persistence
boundaries. Run them once on default temporary storage and once with
`AXEYUM_FS_FIXTURE_PARENT=.`; they remain local process-interruption evidence,
not NFS or power-loss evidence.
Six E1b integration tests add exact-byte preflight, deterministic
interruption/resume equivalence, real kills before/during solver execution,
lease contention/recovery, timeout-response admission, sidecar mutation, and
complete-only raw export. Five runner tests freeze typed exit/signal/resource
states and byte-exact output. E2 adds portable resource-contract tests plus
live delegated user-systemd/cgroup-v2 tests for exact aggregate limits, bounded
two-worker execution, evidence mutation, host-runner kill, and explicit resumed
completion. `./scripts/check-smtcomp-resume.sh` runs the portable bounded gate;
`AXEYUM_REQUIRE_SMTCOMP_CGROUP=1` makes live E2 support mandatory. E3's
registered `s5`/`s6`/`s7` gate is separately mandatory with
`AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1`.

## Reproduce

```sh
# self-contained local run (builds the axeyum CLI, scores vs cvc5 + bitwuzla):
scripts/smtcomp_repro/run_repro.sh corpus/qfbv-curated 20 40 single_query

# Small local shard experiment only. Current raw dumping is end-of-shard and
# must not be used for a large distributed run before ADR-0344 E3:
python3 scripts/smtcomp_repro/compete.py --corpus corpus/qfbv-curated \
    --solver axeyum=target/release/examples/smtcomp_cli \
    --shard 0/2 --dump-raw /tmp/raw0.json ...        # local
ssh s0 'cd <repo> && python3 .../compete.py ... --shard 1/2 --dump-raw <shared>/raw1.json ...'
python3 scripts/smtcomp_repro/compete.py --score-raw /tmp/raw0.json <shared>/raw1.json
```

The failed full-tree attempt and required replacement protocol are documented
in the
[`full-library handoff`](../../docs/plan/smtcomp-full-library-candidate-run-handoff-2026-07-21.md)
and generated
[`resumable-run contract`](../../docs/plan/generated/smtcomp-resumable-run-contract.md).
The local kill-tested boundary is in the
[`E1a result`](../../docs/plan/smtcomp-resumable-filesystem-e1a-2026-07-21.md).
The source-backed v2 process-schema correction and narrow integration seams are
in the [`E1b audit`](../../docs/plan/smtcomp-runner-e1b-audit-2026-07-21.md).
The fixture-only runner implementation is in the
[`E1b result`](../../docs/plan/smtcomp-resumable-runner-e1b-2026-07-22.md).
The one-host aggregate enforcement result is in the
[`E2 result`](../../docs/plan/smtcomp-one-host-resource-enforcement-e2-2026-07-22.md).
The accepted multi-host result is in the
[`E3 result`](../../docs/plan/smtcomp-multi-host-durability-e3-2026-07-22.md).
The independent official-selection boundary is in
[ADR-0356](../../docs/research/09-decisions/adr-0356-preregister-official-smtcomp-selection-identity.md)
and its
[`S0--S5 plan`](../../docs/plan/smtcomp-official-selection-identity-plan-2026-07-22.md).

## Tracks

Single Query, Incremental, Unsat-Core, Model-Validation, Parallel — the tuple
rules for each live in `scoring.py::benchmark_score`.

## Fidelity checks

- Unit tests (`tests/`) hand-verify every tuple/ordering/ranking rule.
- Cross-validation: synthetic result tables scored here vs. the official
  `smtcomp` tool (cloned into gitignored `references/`), see `xcheck/`.

## Not upstream

This directory never opens a PR against SMT-COMP. It is our private measuring
tape.
