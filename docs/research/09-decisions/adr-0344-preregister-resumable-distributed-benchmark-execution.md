# ADR-0344: Preregister resumable distributed benchmark execution

Status: proposed
Date: 2026-07-21

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

## Decision

**Require immutable per-result checkpoints, exact run identity, explicit
attempt accounting, complete shard manifests, strict central merge, and
enforced aggregate resources before any large distributed candidate rerun.**

Specifically:

- a run identity binds corpus/selection, solver/command, runner/repository,
  limits, shard mapping, and measurement environment;
- each solver/benchmark result is self-hashed and atomically installed under a
  key that includes normalized benchmark ID, exact input hash, and solver ID;
- resume skips only a completely validating immutable record and never
  overwrites a prior record;
- every launch attempt is retained; a later shard completion must explicitly
  account for an older terminal-less crash rather than inventing a terminal;
- central merge rejects missing, unexpected, duplicated, conflicting,
  truncated, identity-drifted, wrong-environment, or non-complete inputs;
- no partial merge flows into scoring or a published decide-rate; and
- per-process limits are accompanied by recorded aggregate cgroup-v2 or
  equivalent enforcement and a non-overcommit preflight.

Individual immutable record files are the v1 persistence unit. Append-only
JSONL remains an alternative only if it later proves an equally fail-closed
framing, tail-recovery, fsync, conflict, and restart contract.

## Evidence and preregistered gates

1. The machine-readable contract has one canonical JSON encoding, 14 uniquely
   identified invariants, and a generated human-readable view.
2. Twenty-two executable scenarios include four accepted controls and 18
   rejected mutations covering solver/list/limit/runner/environment drift,
   record tampering/truncation, duplicates, missing/unexpected results,
   assignment overlap, incomplete shards, attempt-accounting failure, and
   aggregate-resource failure.
3. On deterministic fake results, uninterrupted, reordered, and
   interrupted/resumed bundles produce byte-identical canonical merged output.
4. Production stage E1 must kill a real fake-solver process at each persistence
   boundary and reproduce the uninterrupted canonical output before remote
   execution is enabled.
5. Production stage E2 must demonstrate one-host aggregate enforcement and
   fail-before-launch overcommit/environment mutations.
6. Production stage E3 must preserve records and account for attempts across a
   simulated host loss under N>=3 tiny-corpus repetitions.
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
- The v1 prototype passes all 22 declared scenarios and exact recovery
  equivalence without launching a solver or consuming the external corpus.

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
- **Allow identical duplicates at merge.** Rejected for v1: correct resume
  skips an existing record, so duplicates reveal overlapping ownership or
  orchestration drift.
- **Move immediately to BenchExec.** Deferred until selection and environment
  provenance are complete. BenchExec is the official-style rehearsal path, but
  it does not remove the need to freeze exact Axeyum run identities and preserve
  local pre-rehearsal evidence.

## Consequences

Large runs become restartable without mixing configurations or hiding failed
attempts. Completeness is explicit, duplicate overwrite disappears, and
resource control becomes a measured part of the experiment.

The cost is more artifact structure and a staged implementation before another
large run. Result files must remain immutable, retries need fresh attempt IDs,
environment classes need definition, and production filesystem durability must
be tested rather than assumed. G1 advances E1-E3 before corpus execution; the
official-style selection ledger and neutral-oracle runs remain separate work.
