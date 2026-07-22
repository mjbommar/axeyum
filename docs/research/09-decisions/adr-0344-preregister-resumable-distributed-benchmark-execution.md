# ADR-0344: Preregister resumable distributed benchmark execution

Status: accepted
Date: 2026-07-21
Accepted: 2026-07-22

## Context

G1's first 64,345-case candidate run launched 52 shards and retained 2,041
human progress lines before all workers terminated without a traceback. It
produced zero raw shard artifacts because `compete.py` serializes results only
after an entire shard returns. The distributor records neither durable attempt
state nor aggregate host resource enforcement, and central raw merge silently
overwrites duplicate benchmark/solver keys.

The cause of the termination is unknown; remote kernel logs are unavailable.
Regardless of cause, the current pipeline cannot turn an interrupted large run
into auditable partial evidence or safely resume it. The
[frozen handoff](../../plan/smtcomp-full-library-candidate-run-handoff-2026-07-21.md),
[design](../../plan/smtcomp-resumable-run-design-2026-07-21.md), and generated
[contract matrix](../../plan/generated/smtcomp-resumable-run-contract.md)
provide the evidence for this decision.

The concrete E3 shared-storage mechanism and N>=3 destructive controls are
preregistered in the
[E3 plan](../../plan/smtcomp-multi-host-durability-e3-plan-2026-07-22.md).
It binds the exact observed NFSv4.1 host class, preallocated initial/retry
ownership, content-addressed source staging, remote allocation attempts,
fail-closed lease recovery, and multi-host completion before implementation.

## Decision

**Require immutable per-result checkpoints, exact run identity, explicit
attempt accounting, complete shard manifests, strict central merge, and
enforced aggregate resources before any large distributed candidate rerun.**

Specifically:

- a single-solver run identity binds corpus/selection, solver configuration,
  runner/source/toolchain, limits, policies, shard mapping, and measurement
  environment;
- each solver/benchmark result is self-hashed and atomically installed under a
  key that includes normalized benchmark ID, exact input hash, and solver-
  configuration identity;
- each result names its installing attempt, retains observed and scoring-
  admitted verdicts separately, uses a typed termination state, and content-
  addresses stdout/stderr;
- resume skips only a completely validating immutable record and never
  overwrites a prior record;
- every launch attempt is retained; a later shard completion must explicitly
  account for an older terminal-less crash rather than inventing a terminal;
- central merge rejects missing, unexpected, duplicated, conflicting,
  truncated, identity-drifted, wrong-environment, or non-complete inputs;
- no partial merge flows into scoring or a published decide-rate; and
- per-process limits are accompanied by recorded aggregate cgroup-v2 or
  equivalent enforcement and a non-overcommit preflight.

Individual immutable record files are the v2 persistence unit. The preserved
v1 prototype is superseded before integration because it lacked real-process
and attempt-attribution evidence. Append-only
JSONL remains an alternative only if it later proves an equally fail-closed
framing, tail-recovery, fsync, conflict, and restart contract.

## Evidence and preregistered gates

1. The active v2 machine-readable contract has one canonical JSON encoding, 18 uniquely
   identified invariants, and a generated human-readable view.
2. Twenty-eight executable scenarios include five accepted controls and 23
   rejected mutations covering solver/list/limit/runner/environment drift,
   record tampering/truncation, duplicates, missing/unexpected results,
   assignment overlap, incomplete shards, attempt-accounting failure, and
   aggregate-resource failure, typed termination, output identity, late-
   response admission, and per-result attempt/terminal attribution.
3. On deterministic fake results, uninterrupted, reordered, and
   interrupted/resumed bundles produce byte-identical canonical merged output.
4. Production stage E1 must kill a real fake-solver process at each persistence
   boundary and reproduce the uninterrupted canonical output before remote
   execution is enabled.
5. Production stage E2 must demonstrate one-host aggregate enforcement and
   fail-before-launch overcommit/environment mutations.
6. Production stage E3 must preserve records and account for attempts across a
   registered host-runner loss under N>=3 tiny-corpus repetitions.
7. Only a new, complete E4 directory may run the 64,345-file candidate. The
   frozen failed attempt remains unchanged and receives zero result credit.
8. All generated-contract, SMT-COMP reproduction, parity-documentation, link,
   formatting, and diff gates pass under the bounded sequential policy.

These gates authorize reliable local measurement infrastructure only. They do
not authorize an official-selection, representativeness, solver-performance,
coverage, soundness, or OOM-cause claim.

## Evidence

- The first attempt has 52 logs, zero raw JSON shards, and no surviving worker;
  its exact selection hashes and failure snapshot are frozen in the handoff.
- `compete.py` accumulates the shard before end-only `json.dump`, and
  `raw_from_json` overwrites duplicate keys by assignment.
- `distribute_run.sh` launches detached workers but persists no PID, terminal,
  completion, lease, or aggregate-resource artifact.
- The official
  [SMT-COMP 2026 rules](https://smt-comp.github.io/2026/rules.pdf) use BenchExec
  for execution. BenchExec's
  [documentation](https://github.com/sosy-lab/benchexec/blob/main/doc/benchexec.md)
  binds tasks and resource limits and emits individual execution measurements;
  a later official-style rehearsal should use that external layer.
- The v2 prototype passes all 28 declared scenarios and exact scoring-
  projection recovery equivalence without launching a solver or consuming the
  external corpus. It preserves v1 as an explicitly superseded sketch.
- The follow-on
  [E1a filesystem result](../../plan/smtcomp-resumable-filesystem-e1a-2026-07-21.md)
  passes 8/8 real `SIGKILL` recovery cells across local tmpfs and ext-family
  storage. Identical resume skips, conflicts and truncated temporaries are
  quarantined, filename/key drift rejects, and canonical output remains equal.
  This is process-interruption evidence, not power-loss, NFS, launcher, cgroup,
  or multi-host evidence.
- The [E1b runner audit](../../plan/smtcomp-runner-e1b-audit-2026-07-21.md)
  finds that the active executor discards a parsed verdict on wall timeout,
  contrary to SMT-COMP 2026 section 7.1.2, and guesses that every other signal
  means memory exhaustion. V2 represents observed/admitted verdicts and typed
  process outcomes without granting a retroactive result correction.
- The [E1b runner result](../../plan/smtcomp-resumable-runner-e1b-2026-07-22.md)
  integrates exact preflight, immutable attempts/results/output sidecars,
  typed termination, explicit lease recovery, completion-last publication,
  and fail-closed raw export into the active runner on committed fixtures.
- The [E2 one-host result](../../plan/smtcomp-one-host-resource-enforcement-e2-2026-07-22.md)
  passes the required live delegated user-systemd/cgroup-v2 gate. It enforces
  and reads back exact aggregate memory, zero swap, CPU bandwidth, and PID
  limits over a bounded worker pool; records controller counters; rejects
  overcommit and environment drift before launch; and preserves honest
  terminal-less resource sessions across destructive host-runner kill/resume.
- The [E3 multi-host result](../../plan/smtcomp-multi-host-durability-e3-2026-07-22.md)
  passes the required `s5`/`s6`/`s7` NFSv4.1 gate twice at one committed source
  identity. Six results survive an exact marker-bound host-runner `SIGKILL`,
  dead-unit/launcher proof, deterministic stale-lease quarantine, and
  preregistered different-host retry. The interrupted and uninterrupted
  timing-free outcome projections are byte-identical; lifecycle evidence
  differs exactly as registered.

## Alternatives

- **Rerun unchanged with fewer workers.** Rejected: lower concurrency may avoid
  one failure cause but does not preserve results or establish resume identity.
- **Recover records from progress logs.** Rejected: logs omit the complete
  machine schema and were not designed as an atomic evidence source.
- **Write JSONL and ignore a malformed final line.** Deferred: silent tail
  repair can hide corruption; an explicit framing/quarantine protocol would
  need the same mutation gates as immutable files.
- **Require every attempt to emit a terminal.** Rejected: SIGKILL, host loss,
  and OOM can prevent it. Absence must be observable and later accounted, not
  made impossible by specification.
- **Allow identical duplicates at merge.** Rejected for v2: correct resume
  skips an existing record, so duplicates reveal overlapping ownership or
  orchestration drift.
- **Move immediately to BenchExec.** Deferred until selection and environment
  provenance are complete. BenchExec is the official-style rehearsal path, but
  it does not remove the need to freeze exact Axeyum run identities and preserve
  local pre-rehearsal evidence.

## Consequences

Large runs can become restartable without mixing configurations or hiding
failed attempts. E1a proves the local record primitive. The subsequent
[E1b result](../../plan/smtcomp-resumable-runner-e1b-2026-07-22.md) integrates
exact preflight, typed execution, sidecars, attempts, leases, completion-last
export, and duplicate rejection into a fixture-only `compete.py` mode. E2 is
now complete: the one-host adapter and its immutable resource evidence pass the
required live cgroup-v2 gate. E3 is now complete for the registered three-host
shared-NFSv4.1 class; the independent official selection ledger is the next G1
prerequisite.

The cost is more artifact structure and a staged implementation before another
large run. Result files must remain immutable, retries need fresh attempt IDs,
environment classes need definition, and production filesystem durability must
be tested rather than assumed. G1 retains the completed E3 gate before corpus execution; the
official-style selection ledger and neutral-oracle runs remain separate work.
