# SMT-COMP resumable runner E2 one-host enforcement result

Status: accepted one-host aggregate enforcement; E3 multi-host durability remains open
Date: 2026-07-22

## Outcome

The resumable runner now has a real one-host execution path:

```sh
python3 scripts/smtcomp_repro/compete.py --host-run \
  --run-manifest RUN.json --run-dir EVIDENCE ...
```

`--host-run` launches one transient user-systemd service whose cgroup contains
the host runner, its bounded shard-worker pool, every solver process, and all
descendants. The run identity binds the content-derived enforcement descriptor
in addition to the E1 solver, corpus, selection, source, toolchain, environment,
and output identities. The adapter rejects fixture envelopes, memory/CPU/PID
overcommit, and environment drift before the service or solver is launched.

Inside the service, preflight validates the registered cgroup-v2 path, inode,
controller set, `memory.max`, zero `memory.swap.max`, `cpu.max`, `pids.max`, and
current membership before changing delegated state. The one OOM-group setting
unavailable as a transient unit property is then written and read back as
`memory.oom.group=1`; the complete snapshot and baseline counter maps are
validated before the immutable preflight is installed. Only then may shard
workers start.

The resource terminal records worker exit codes, `memory.peak`, `pids.peak`,
and nonnegative deltas for `memory.events`, `cpu.stat`, and `pids.events`.
Every measurement attempt names its resource session. A killed host runner
cannot write a terminal; that absence remains explicit in the final
`unclosed_session_ids` just as E1 preserves terminal-less shard attempts. Raw
JSON export now requires the complete result bundle and complete, self-hashed
E2 resource evidence.

This closes E2 on one host. It does not establish shared-filesystem durability,
host allocation, spool transfer, environment-class equivalence across hosts,
or loss/retry under N>=3 hosts. Those remain E3, and the independent official
selection ledger is still required before a credited large run.

## Implementation

- `scripts/smtcomp_repro/resource_enforcement.py` defines exact enforcement
  descriptors, live cgroup preflight, immutable session/terminal/completion
  evidence, systemd launch properties, bounded worker scheduling, and strict
  validation before export.
- `scripts/smtcomp_repro/compete.py --host-run` owns the aggregate service and
  launches all registered shards with at most `worker_slots` concurrent.
- `scripts/smtcomp_repro/resume_runner.py` binds the enforcement digest into run
  identity and attributes every E2 attempt to one resource session.
- `scripts/smtcomp_repro/resume_fs.py` admits the exact resource namespace and
  requires its validation for score export.
- `scripts/smtcomp_repro/fixtures/e2/` is the committed four-case concurrency
  corpus plus one kill-after-start case and deterministic fake solver.

## Executable gates

Run the complete E0-E2 gate on a delegated user-systemd host:

```sh
AXEYUM_REQUIRE_SMTCOMP_CGROUP=1 ./scripts/check-smtcomp-resume.sh
```

The E0-E2 aggregate passes 17 `unittest` cases on this host. The E2 portion
proves:

- exact content-derived descriptor and run-identity binding;
- fail-before-service memory, CPU, and PID overcommit rejection;
- fail-before-service environment-class drift rejection;
- a real two-worker service with 128 MiB aggregate memory, zero swap, a
  `200000 100000` CPU limit, and `pids.max=64` over four committed cases;
- nonzero observed memory peak, CPU usage, and PID peak in the immutable
  terminal;
- tampered resource evidence blocks raw export; and
- killing the in-cgroup host runner leaves both the attempt and resource
  session terminal-less, systemd kills the remaining control group, explicit
  lease recovery succeeds, and a second session completes the run while naming
  the prior unclosed session.

If user-systemd or cgroup v2 is unavailable, the ordinary repository gate runs
the portable descriptor/controller tests and reports the live cells as skipped.
Setting `AXEYUM_REQUIRE_SMTCOMP_CGROUP=1` makes absence fail closed; this is the
required setting for E2 evidence and any real measurement host.

## Bounded claim

E2 authorizes one-host execution mechanics only. It does not label an arbitrary
signal as OOM, and session-level counter deltas do not by themselves attribute
one aggregate event to a particular concurrent solver. Individual result
termination remains typed from direct evidence; aggregate kernel events remain
in the resource terminal. It is not BenchExec and is not an official SMT-COMP
result.

Next: E3 must allocate disjoint work to at least three registered hosts, prove
host-loss retry and transfer/shared-storage durability, and produce a complete
canonical merge before the official-style selection and P0 slice reruns.
