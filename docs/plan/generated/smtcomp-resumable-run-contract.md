# Resumable SMT-COMP-style run contract v2

> **Generated; do not edit by hand.** Source: [`docs/plan/smtcomp-resumable-run-contract-v2.json`](../smtcomp-resumable-run-contract-v2.json). Regenerate with `python3 scripts/gen-smtcomp-resume-contract.py`.

Status: prototype; supersedes v1 before production integration; no full-library rerun is authorized.

## Result

- Invariants: **18**
- Executable scenarios: **28** (5 accepted controls, 23 rejected mutations)
- Interrupted/resumed scoring projection byte-identical to uninterrupted: **true**
- Response observed before a forced timeout remains admitted: **true**
- Canonical baseline SHA-256: `31f0271a5e34e951aedfacded5f436a9d906684e032b3f4efce62623e9c95588`

## Why v1 was insufficient

- Attribute every result to the attempt that installed it.
- Retain observed solver response separately from the response admitted to scoring.
- Use a typed termination class instead of an ambiguous memory-exceeded boolean.
- Retain exit, signal, resource-limit, peak-RSS, and content-addressed output facts.
- Separate the scoring wall time, which is bounded by the registered limit, from runner elapsed time that may include watchdog kill and reap overhead.
- Partition each terminal's durable result set into newly installed and skipped prior records.
- Bind verdict-admission, output-capture, resource, toolchain, source-tree, and solver-configuration policies into run identity.

## Invariants

- **R1** — Run identity binds corpus, selection, one solver configuration, runner, source tree, toolchain, limits, shard mapping, policies, and measurement environment before launch.
- **R2** — A result key binds normalized benchmark identity, exact input bytes, and solver-configuration identity.
- **R3** — Each assigned result key belongs to exactly one shard; overlapping or unassigned records are rejected.
- **R4** — Each immutable result record is self-hashed and installed atomically; malformed, truncated, or hash-mismatched records are rejected.
- **R5** — Resume skips only an existing record whose key, content hash, and complete run identity validate; it never overwrites a record.
- **R6** — Any duplicate record presented to central merge is an orchestration defect and is rejected, even when byte-identical.
- **R7** — Every launch attempt has an immutable launch manifest; a missing terminal is preserved and explicitly accounted by a later shard completion manifest.
- **R8** — A shard is complete only when all and only assigned keys validate, its result-set hash matches, and every launch attempt is terminal or explicitly recorded as unclosed.
- **R9** — Central merge rejects missing or non-complete shard manifests and never treats partial coverage as a scoreable run.
- **R10** — Per-process and aggregate host memory limits have named enforcement identities; declared concurrency cannot exceed the enforced aggregate budget.
- **R11** — Every result uses the preregistered environment class; a retry on a different class is a new measurement run.
- **R12** — Canonical scoring projection is independent of shard, host, attempt, and filesystem enumeration order.
- **R13** — On a deterministic fake-solver fixture, interrupted-plus-resumed and uninterrupted canonical scoring bytes are identical even though lifecycle evidence differs.
- **R14** — Temporary, conflicting, malformed, and failed-attempt artifacts are retained outside the accepted immutable record set.
- **R15** — Observed solver response and scoring-admitted response are separate; the SMT-COMP 2026 policy admits a response even after timeout or abnormal termination.
- **R16** — Termination is a checked tagged state over exit, signal, and evidenced resource-limit facts; an arbitrary signal is never relabeled as memory exhaustion, and scoring wall time remains bounded separately from runner overhead.
- **R17** — Every result names its installing attempt, and each terminal partitions its durable keys into disjoint newly installed and previously skipped sets.
- **R18** — Stdout and stderr are content-addressed with exact byte counts; production validation must verify their sidecars before score export.

## Failure and recovery matrix

| ID | Scenario | Expected | Observed | Baseline bytes | Contract result |
|---|---|---:|---:|---:|---|
| F01 | `uninterrupted` | accept | accept | true | validated |
| F02 | `interrupted_resume` | accept | accept | true | validated |
| F03 | `reordered_artifacts` | accept | accept | true | validated |
| F04 | `solver_identity_drift` | reject | reject | n/a | solver configuration digest mismatch |
| F05 | `selection_identity_drift` | reject | reject | n/a | record run identity mismatch |
| F06 | `limit_identity_drift` | reject | reject | n/a | record run identity mismatch |
| F07 | `runner_identity_drift` | reject | reject | n/a | record run identity mismatch |
| F08 | `record_hash_tamper` | reject | reject | n/a | observed verdict was not admitted |
| F09 | `record_run_identity_drift` | reject | reject | n/a | record run identity mismatch |
| F10 | `conflicting_duplicate` | reject | reject | n/a | runner elapsed time is below scoring wall time |
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
| F23 | `attempt_attribution_drift` | reject | reject | n/a | terminal new-result attribution mismatch |
| F24 | `illegal_termination_state` | reject | reject | n/a | illegal typed termination state |
| F25 | `invalid_output_identity` | reject | reject | n/a | invalid SHA-256 field: stdout_sha256 |
| F26 | `timeout_response_retained` | accept | accept | false | validated |
| F27 | `terminal_attribution_mismatch` | reject | reject | n/a | terminal new/skipped partition mismatch |
| F28 | `scoring_time_out_of_range` | reject | reject | n/a | scoring wall time exceeds registered limit |

## Explicit declines

- V2 is a single-solver run contract; a multi-solver invocation must split into one run identity per solver configuration before central comparison.
- This prototype does not make the 2024 cap/family selection official or representative.
- It does not yet integrate compete.py, verify stdout/stderr sidecars, execute solvers, launch remotely, enforce cgroups, prove NFS durability, or manage leases.
- It does not claim real solver timing is byte-identical across retries; byte identity applies to a deterministic scoring-projection fixture.
- It does not admit partial shards, human progress logs, guessed resource causes, or reconstructed records into scoring.
- It does not replace BenchExec for an official competition rehearsal.

## Implementation boundary

The v2 in-memory and E1a filesystem prototypes validate evidence shape, attribution, no-overwrite persistence, and canonical scoring projection. E1b still has to integrate one-solver run manifests, exact benchmark IDs/hashes, output sidecars, typed process outcomes, attempt lifecycle, completion-last export, duplicate rejection, and a fake solver into `compete.py` without changing central scoring semantics.

The current runner drops a parsed response on wall timeout and labels any other signal as memory exhaustion. V2 deliberately cannot encode those guesses as valid SMT-COMP evidence: observed and admitted verdicts are separate, and memory-limit classification requires actual enforcement evidence.
