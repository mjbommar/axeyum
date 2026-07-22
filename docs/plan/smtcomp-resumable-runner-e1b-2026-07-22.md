# SMT-COMP resumable runner E1b result

Status: accepted fixture integration; real measurement execution remains blocked on E2-E3
Date: 2026-07-22

## Outcome

The active local runner now has an opt-in v2 evidence path behind
`compete.py --run-manifest ... --run-dir ...`. It completes ADR-0344's E1b
runner/solver integration without changing legacy small-run scoring artifacts.
The new path deliberately rejects every non-fixture resource envelope, so this
result authorizes reliability testing only—not the 64,345-file rerun or any
performance/coverage claim.

Before a solver starts, the adapter validates one exact run identity over:

- the ordered selected-list bytes and a canonical per-benchmark ledger of
  normalized ID, exact SHA-256, and byte count;
- selection, corpus, and environment artifacts;
- one solver ID, executable bytes, and command template;
- runner sources, repository commit, dirty-tree content, Python toolchain, and
  output/resource policies; and
- track, wall/CPU/memory/core limits, shard count, and striped assignment.

Execution then acquires one no-steal shard lease, installs an immutable launch
manifest, skips only complete record-plus-sidecar checkpoints, captures exact
stdout/stderr bytes, writes a self-hashed typed result, installs a separate
best-effort terminal, and publishes shard completion last. Explicit stale
recovery must name the old lease owner; age alone never steals a lease.

The v2 path preserves an observed `sat`/`unsat`/`unknown` even when the watchdog
fires, as required by its registered SMT-COMP 2026 response policy. It records
wall timeout, ordinary signal, nonzero exit, evidenced CPU/memory limit, and
runner error as distinct states. An arbitrary negative POSIX return code is no
longer guessed to be memory exhaustion. Scoring wall time is clamped separately
from watchdog kill/reap elapsed time, and Linux `VmHWM` is sampled as fixture
diagnostic evidence.

Legacy raw JSON is exported only after every shard completion, record,
attempt, and output sidecar validates. `raw_from_json` now rejects both
identical and conflicting duplicate benchmark/solver cells instead of silently
overwriting them.

## Implementation

- `scripts/smtcomp_repro/resume_runner.py`: preflight, exact selection ledger,
  assignments, active execution, result/attempt/completion construction, and
  complete-only compatibility export.
- `scripts/smtcomp_repro/resume_fs.py`: exact-byte immutable sidecars,
  single-owner leases with explicit recovery, split launch/terminal loading,
  and sidecar validation.
- `scripts/smtcomp_repro/runner.py`: byte-exact capture, timeout-observed
  response retention, typed termination, bounded scoring time, and sampled RSS.
- `scripts/smtcomp_repro/compete.py`: fixture-only `--run-manifest` /
  `--run-dir` mode while retaining legacy mode.
- `scripts/check-smtcomp-resume.sh`: the required E0/E1 regression gate,
  registered in `just check`, the shell fallback, and CI.

## Executable gates

The E1b suite proves the preregistered boundary with real processes and
deterministic projections:

- a selected benchmark byte mutation rejects before the run directory or
  solver exists;
- `SIGKILL` before solver start leaves an immutable launch with no invented
  terminal, and resume accounts it in `unclosed_attempt_ids`;
- `SIGKILL` of the runner during an active fake solver is followed by explicit
  lease recovery and a complete validating resume;
- a concurrent second process targeting that shard fails lease preflight;
- an interrupted two-result attempt plus resume produces byte-identical
  canonical scoring output to the uninterrupted fixed-metric control, with
  exact old/new/skipped attempt partitions;
- a fake solver emits `sat` then hangs; its result remains admitted while the
  typed termination is `wall-timeout`;
- nonzero exit, operator signal, evidenced memory-limit termination, and
  non-UTF-8 output remain distinct and byte exact;
- mutating an output sidecar blocks compatibility export; and
- the four E1a persistence phases remain covered by the existing real
  `SIGKILL` matrix.

Run:

```sh
./scripts/check-smtcomp-resume.sh
AXEYUM_FS_FIXTURE_PARENT=. PYTHONWARNINGS=error \
  python3 -m unittest scripts.tests.test_smtcomp_resume_fs
```

The aggregate gate currently covers 10 `unittest` cases (four E1a plus six
E1b), five typed-runner cases, 30 scoring cases, six pipeline cases, five
selection cases, two provenance cases, and the generated 18-invariant /
28-scenario v2 contract.

## Deliberate boundary and next action

E1b grants no measurement credit. It does not provide a real cgroup-v2
aggregate envelope, prove `/nas3` durability, transfer a host-local spool,
recover a lost remote host, or make the 2024 cap/family candidate an official
selection. The exact selection-input ledger used by E1b is a necessary identity
check, not the still-missing official eligibility/status/difficulty ledger.

E2 is next: add a real one-host aggregate enforcement adapter, fail before
solver launch on overcommit/environment drift, and exercise process/runner
kills on a tiny committed corpus. E3 then owns N>=3 multi-host allocation,
shared-filesystem or spool-transfer durability, host-loss recovery, and
canonical complete-run equivalence. The large candidate remains forbidden
until E2-E3 and the independent official-style selection ledger pass.
