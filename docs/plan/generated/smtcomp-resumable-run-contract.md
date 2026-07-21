# Resumable SMT-COMP-style run contract

> **Generated; do not edit by hand.** Source: [`docs/plan/smtcomp-resumable-run-contract-v1.json`](../smtcomp-resumable-run-contract-v1.json). Regenerate with `python3 scripts/gen-smtcomp-resume-contract.py`.

Status: prototype; no full-library rerun is authorized by this artifact.

## Result

- Invariants: **14**
- Executable scenarios: **22** (4 accepted controls, 18 rejected mutations)
- Interrupted/resumed deterministic fixture byte-identical to uninterrupted: **true**
- Canonical baseline SHA-256: `eb60ed595cd30a90bd500b63793670a67c14005c1b570fabc75b8f38c77e98ee`

## Invariants

- **R1** — Run identity binds corpus, selection, solver, runner, repository, limits, shard mapping, and measurement environment before launch.
- **R2** — A result key binds normalized benchmark identity, exact input bytes, and solver identity.
- **R3** — Each assigned result key belongs to exactly one shard; overlapping or unassigned records are rejected.
- **R4** — Each immutable result record is self-hashed and installed atomically; malformed, truncated, or hash-mismatched records are rejected.
- **R5** — Resume skips only an existing record whose key, content hash, and complete run identity validate; it never overwrites a record.
- **R6** — Any duplicate record presented to central merge is an orchestration defect and is rejected, even when byte-identical.
- **R7** — Every launch attempt has an immutable launch manifest; a missing terminal is preserved and explicitly accounted by a later shard completion manifest.
- **R8** — A shard is complete only when all and only assigned keys validate, its result-set hash matches, and every launch attempt is terminal or explicitly recorded as unclosed.
- **R9** — Central merge rejects missing or non-complete shard manifests and never treats partial coverage as a scoreable run.
- **R10** — Per-process and aggregate host memory limits have named enforcement identities; declared concurrency cannot exceed the enforced aggregate budget.
- **R11** — Every result uses the preregistered environment class; a retry on a different class is a new measurement run.
- **R12** — Canonical merge order is independent of shard, host, attempt, and filesystem enumeration order.
- **R13** — On a deterministic fake-solver fixture, interrupted-plus-resumed and uninterrupted canonical result bytes are identical.
- **R14** — Temporary, conflicting, malformed, and failed-attempt artifacts are retained outside the accepted immutable record set.

## Failure and recovery matrix

| ID | Scenario | Expected | Observed | Canonical bytes | Contract result |
|---|---|---:|---:|---:|---|
| F01 | `uninterrupted` | accept | accept | true | validated |
| F02 | `interrupted_resume` | accept | accept | true | validated |
| F03 | `reordered_artifacts` | accept | accept | true | validated |
| F04 | `solver_identity_drift` | reject | reject | n/a | record run identity mismatch |
| F05 | `selection_identity_drift` | reject | reject | n/a | record run identity mismatch |
| F06 | `limit_identity_drift` | reject | reject | n/a | record run identity mismatch |
| F07 | `runner_identity_drift` | reject | reject | n/a | record run identity mismatch |
| F08 | `record_hash_tamper` | reject | reject | n/a | record hash mismatch |
| F09 | `record_run_identity_drift` | reject | reject | n/a | record run identity mismatch |
| F10 | `conflicting_duplicate` | reject | reject | n/a | duplicate result record |
| F11 | `identical_duplicate` | reject | reject | n/a | duplicate result record |
| F12 | `missing_record` | reject | reject | n/a | missing assigned result records |
| F13 | `unexpected_record` | reject | reject | n/a | unexpected or wrong-shard result record |
| F14 | `missing_shard_completion` | reject | reject | n/a | missing or unexpected shard completion |
| F15 | `wrong_result_set_hash` | reject | reject | n/a | completion result-set hash mismatch |
| F16 | `overlapping_assignment` | reject | reject | n/a | overlapping shard assignment |
| F17 | `unaccounted_crash` | reject | reject | n/a | unaccounted terminal-less attempt |
| F18 | `accounted_prior_crash` | accept | accept | true | validated |
| F19 | `missing_resource_enforcement` | reject | reject | n/a | missing aggregate resource enforcement |
| F20 | `aggregate_memory_overcommit` | reject | reject | n/a | aggregate memory budget overcommitted |
| F21 | `environment_class_drift` | reject | reject | n/a | measurement environment drift |
| F22 | `truncated_record` | reject | reject | n/a | record field set mismatch |

## Explicit declines

- This prototype does not make the 2024 cap/family selection official or representative.
- It does not implement remote launch, cgroups, NFS durability, leases, or production signal handling.
- It does not claim real solver timing is byte-identical across retries; byte identity is a deterministic fixture gate for checkpoint semantics and canonical ordering.
- It does not admit partial shards, human progress logs, or reconstructed records into scoring.
- It does not replace BenchExec for an official competition rehearsal.

## Implementation boundary

The prototype validates the data and lifecycle contract in memory. Production work still has to implement same-directory temporary writes plus fsync/rename, immutable launch and terminal manifests, single-owner shard leases, cgroup-v2 (or equivalent) aggregate enforcement, signal-safe best-effort terminal emission, conflict quarantine, and strict central merge over real filesystem artifacts. A tiny fake-solver process test must kill an actual worker at fixed record boundaries before the 64,345-case candidate can be rerun.

BenchExec remains the external reference execution layer for official-style rehearsal; this local protocol exists to make Axeyum's pre-rehearsal distributed evidence durable and auditable.
