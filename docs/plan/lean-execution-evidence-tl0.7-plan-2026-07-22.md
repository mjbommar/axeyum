# TL0.7 plan — Lean execution resources, attempts, and completion evidence

Status: **preregistered; no process-runner or execution observation yet**

Date: 2026-07-22

Owner: complete Lean-parity documentation/evidence lane

Parent tasks and decisions:

- [`TL0.7`](lean-system-implementation-plan-2026-07-21.md#tl07-lean-execution-evidence-slices)
- [`TL0.6.3`](lean-system-implementation-plan-2026-07-21.md#tl06-u2-official-test-execution-slices)
- [complete Lean 4.30 parity contract](lean4-complete-parity-contract-2026-07-22.md)
- [ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md)
- [ADR-0344](../research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md)

## 1. Decision boundary

TL0.7 supplies the evidence protocol required before a Lean process result may
flow into TL0.6.3 or any terminal parity cell. It does not run Lean, CTest, an
exporter, or Axeyum; it cannot create an official outcome, completed case,
paired cell, denominator, performance datum, or parity credit.

The implementation must separate four things that are often collapsed:

1. a **lane policy** states which resource and durability mechanisms are
   permitted;
2. a **run identity** freezes exact inputs, executable/configuration,
   environment, limits, selection, and checkpoint policy before launch;
3. an **attempt record** retains what one launch did, including incomplete and
   terminal-less attempts; and
4. a **completion record** is installed last and proves closure over all and
   only the run's assigned cases and attempts.

No human log line, CTest summary, JUnit file, GitHub job conclusion, or process
exit code is sufficient by itself.

## 2. Frozen input identities

The contract implementation must bind these current inputs by exact bytes:

| Input | SHA-256 | Role |
|---|---|---|
| `lean-u2-official-ci-profiles-v1.json` | `4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548` | 17 contexts, 153 cells, 111 declared attempts, exact selected case IDs |
| `lean-complete-parity-v1.json` | `f2fc71509b4f557265a853ebb7666071b7b67d8553c0951ae1f91b736059ab78` | terminal record and no-credit fields |
| `scripts/mem-run.sh` | `25740241696f08480874e7b63214d62cfdf24eef766a3169c59b3af788498c63` | current address-space wrapper boundary |
| ADR-0344 | `3faef4ae21a1b61739812c524d76f1efc2d7e473b1a59d7d3921594ec0a475ed` | immutable records, attempts, completion-last, aggregate-resource precedent |
| ADR-0345 | `7af3ba0c11dd320d2ad9859dd5cac1ba06a25c26e5fee6670095d7fe51386a0a` | Lean adapter/native trust and resource boundary |
| Lean implementation plan | `1e23a4e77be3c4ee348b7c19f88511254045ae17a53c102a5f64ba9384981de4` | 4 GiB default, 8 GiB exporter exception, checkpoint requirement and TL0.7 slices |

The upstream Lean inputs remain pinned at commit
`d024af099ca4bf2c86f649261ebf59565dc8c622` through the TL0.6.2 authority.
The workflow derives `NPROC` from the live runner and gives only its two network
steps explicit 20-minute step timeouts. It declares no job-wide memory cap.
Consequently, a runner label or upstream job definition is configuration
provenance, not proof of actual hardware, effective memory, or completion.

Current GitHub documentation states a default 360-minute job timeout and a
maximum 360-minute step timeout, but provider defaults can change. A credited
run must retain the effective timeout observed or explicitly configured for
that run rather than importing a live documentation default into this pinned
contract. Standard GitHub-hosted and third-party `nscloud-*` labels remain
different provider classes and opaque identifiers until their actual run
environment is captured.

Primary external references:

- [GitHub Actions workflow timeout syntax](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax)
- [GitHub-hosted runner specifications](https://docs.github.com/en/actions/reference/runners/github-hosted-runners)
- [CTest command and result semantics](https://cmake.org/cmake/help/latest/manual/ctest.1.html)
- [GitHub artifact retention](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/remove-workflow-artifacts)

## 3. Machine contract

The planned `axeyum-lean-execution-evidence-v1` authority must define and
validate these record families.

### 3.1 Lane policy

Every lane has a stable ID, purpose, allowed producer, enforcement mechanism,
memory scope, concurrency ceiling, durability class, and parity-credit class.
The first two registered local policies are:

| Lane | Memory rule | Concurrency | Credit boundary |
|---|---|---:|---|
| `standard-local-4g` | explicit 4 GiB (`4,294,967,296` bytes) per-process address-space ceiling | at most two workers | development/contract evidence; not an official platform result |
| `official-export-8g` | explicit 8 GiB (`8,589,934,592` bytes) per-process address-space ceiling | one exporter worker | official adapter/export evidence only; not native parity |

These are ceilings, not claimed peak RSS measurements. The current
`mem-run.sh` default is 64 GiB, so only an explicit `MEM_LIMIT_GB=4` or
`MEM_LIMIT_GB=8` invocation can instantiate these templates. A later official
CTest reproduction lane may use a different envelope, but it must be separately
registered and content-identified; it may not inherit either local lane by
name.

### 3.2 Resource envelope

A concrete run must record, with units and enforcement state:

- wall timeout, CPU-time limit, address-space/memory limit and scope;
- worker, thread, process/PID, swap, disk, and open-file limits;
- enforcement mechanism and immutable evidence artifacts;
- requested and effective parallelism, including resolved `NPROC`;
- actual platform, architecture, kernel/OS/image, CPU, memory, filesystem, and
  provider/runner identity; and
- observed wall time, CPU time, peak RSS, swap, exit status, and relevant
  controller events when available.

Unavailable metrics are typed `not-observed`; unenforced limits are typed
`not-enforced`. Neither may be represented as zero. A run can earn functional
credit with declared non-performance fields only if the profile permits it;
performance or resource-equivalence credit always requires actual matched
observations.

### 3.3 Immutable run identity

Before launch, one digest binds at least:

- schema and producer revisions;
- Lean/Axeyum/external tool pins and executable bytes;
- exact source, dependency, registration, selection-set, and case identities;
- normalized command, working directory, environment, preset/configuration,
  runner/platform class, and network/cache policy;
- complete resource envelope and enforcement/durability policy; and
- assignment/shard mapping plus expected output/JUnit/artifact policy.

Any change creates a new run. A retry is another attempt under the same run
only when the entire run identity remains byte-identical.

### 3.4 Attempt and termination records

Each launch receives a unique immutable attempt ID before process creation.
The attempt retains sequence, start metadata, process-group/runner identity,
assigned cases, exact stdout/stderr identities, observations, and one of these
termination classes:

- `exited`;
- `signaled`;
- `wall-timeout`;
- `cpu-timeout`;
- `memory-limit`;
- `pids-limit`;
- `disk-limit`;
- `cancelled`;
- `runner-lost`;
- `launch-failed`;
- `preflight-invalid`; or
- `unknown-termination`.

Exit codes, signal numbers, timeout/controller events, and producer diagnostics
remain separate fields. `memory-limit` requires an enforcing controller/event
or an exact cooperative limit diagnostic; a signal or nonzero exit alone may
not be guessed as OOM. A killed or lost producer may have no terminal record;
the pre-launch attempt record remains and later completion must account for it.

### 3.5 Case records and raw artifacts

Every selected case has exactly one terminal case record in a completed run.
It binds the TL0.6.1 case identity, TL0.6.2 attempt/selection identity, owning
launch attempt, command, relevant source/support bytes, start/end status,
CTest/JUnit name, output/diagnostic class, raw artifact hashes/sizes, and one of
`passed`, `failed`, `skipped`, `not-run`, or `invalid-run`.

JUnit is an independently parsed sidecar. It must agree with the exact case
population and retained raw evidence; it does not replace case records or prove
run completion. Provider artifacts must be copied into content-addressed
durable storage before their expiration can be ignored; the provider artifact
ID, digest, size, retention/expiry state, and durable copy identity are all
retained.

### 3.6 Checkpoints, resume, and completion

Run, attempt, case, artifact, and completion records use canonical JSON,
self-hashes, same-directory temporary creation, flush/fsync, atomic install,
and directory fsync where the storage class supports it. Existing valid records
are skipped; invalid, different, or duplicate records are conflicts and are
never overwritten.

Resume may add a new attempt and missing immutable case records. It cannot
rewrite an earlier attempt or case. CTest `-F` may be a diagnostic input, but it
does not satisfy this contract without the same independent identity,
attempt-accounting, and exact case-closure validation.

Completion is installed last. It enumerates every expected case, all attempts
including terminal-less ones, exact record-set digests, missing/unexpected/
duplicate counts, and the final typed state. Partial progress can be summarized
only as `incomplete`; it earns zero run, case-denominator, or parity credit.

## 4. Credit predicates

The validator must make these implications executable:

1. no execution credit without an exact pre-launch run identity;
2. no completion credit without all and only assigned case records;
3. no case credit from JUnit, logs, or provider conclusion alone;
4. no resource-limit classification without matching enforcement evidence;
5. no resume that deletes, rewrites, or leaves an earlier attempt unaccounted;
6. no official-platform credit when the actual runner/platform identity is
   absent or differs from the declared profile;
7. no performance comparison without matched effective resources and observed
   metrics;
8. no official adapter/export result promoted to native Axeyum parity;
9. no incomplete or invalid run entering TL0.6 paired denominators; and
10. no broad result from synthetic fixture scenarios.

The committed authority itself must record zero runs, attempts, cases,
completions, official outcomes, Axeyum outcomes, and paired cells.

## 5. Required fail-closed tests

The implementation must reject at least these mutation classes:

1. source/schema/producer identity drift;
2. lane ID, cap, concurrency, purpose, or credit-class drift;
3. implicit use of the 64 GiB wrapper default as the 4/8 GiB lane;
4. missing, zero-valued, unitless, or contradictory resource fields;
5. runner-label substitution without observed platform identity;
6. changed command/environment/working directory/selection under one run ID;
7. attempt omission, duplication, sequence drift, or case-assignment overlap;
8. guessed OOM/timeout/signal classification without matching evidence;
9. missing, duplicate, unexpected, reordered, or identity-drifted case record;
10. case record attributed to the wrong attempt or selection set;
11. stdout/stderr/JUnit/artifact hash or size mutation;
12. JUnit-only or provider-conclusion-only completion;
13. provider artifact without retention and durable-copy state;
14. overwritten/conflicting checkpoint or reused self-hash;
15. completion installed before its dependencies or with the wrong record-set
    digest;
16. terminal-less earlier attempt omitted from resumed completion;
17. incomplete/preflight-invalid run receiving case, denominator, performance,
    or parity credit;
18. adapter/export evidence promoted to native-system credit; and
19. any committed real outcome or terminal promotion in this contract-only
    milestone.

Synthetic accepted controls must cover clean completion, a failed case retained
without disappearing, an interrupted/resumed completion with both attempts,
and diagnostic incomplete/preflight-invalid bundles. They test representation
and validation only; they are not Lean results.

## 6. Milestones and outputs

TL0.7 advances through four reviewable slices:

1. **TL0.7.1 contract:** machine authority, validator, generated review report,
   synthetic accepted/rejected scenarios, and offline CI gate;
2. **TL0.7.2 process adapter:** exact command/environment launch, process-group
   cleanup, typed exit/signal/timeout/limit capture, raw output hashing, and
   forced termination controls under the 4/8 GiB lanes;
3. **TL0.7.3 durable store:** immutable checkpoints, conflict quarantine,
   kill/resume, completion-last publication, and filesystem-specific
   durability evidence; and
4. **TL0.7.4 acceptance:** one no-credit pinned-Lean preflight and one
   official-export control prove the complete path without yet running the U2
   profile population.

Planned TL0.7.1 artifacts:

- `docs/plan/lean-execution-evidence-v1.json`;
- `docs/plan/generated/lean-execution-evidence.json`;
- `docs/plan/generated/lean-execution-evidence.md`;
- `scripts/gen-lean-execution-evidence.py`; and
- `scripts/tests/test_lean_execution_evidence.py`.

## 7. Stop conditions

Stop and retain TL0.7 as partial if:

- a resource or termination class cannot be represented without guessing;
- the implementation needs to execute Lean before the contract is committed;
- a wrapper cannot distinguish requested limits from effective enforcement;
- durable install semantics are assumed rather than tested for the storage
  class;
- a runner/platform label is treated as stable hardware identity;
- partial/JUnit/provider data could be mistaken for completion;
- a source or selection identity drifts; or
- any synthetic control could flow into a real parity denominator.

TL0.7.1 may complete while TL0.7 remains partial. TL0.6.3 stays blocked until
the process and durable-store slices prove that actual official attempts can
be retained under this contract.
