# TL0.7.2 plan — bounded Lean execution process adapter

Status: **preregistered; no process probe or retained observation yet**

Date: 2026-07-22

Owner: complete Lean-parity documentation/evidence lane

Parent:

- [TL0.7 execution-evidence plan](lean-execution-evidence-tl0.7-plan-2026-07-22.md)
- [TL0.7.1 machine-contract result](lean-execution-evidence-tl0.7.1-2026-07-22.md)
- [complete Lean 4.30 parity contract](lean4-complete-parity-contract-2026-07-22.md)
- [`TL0.7.2`](lean-system-implementation-plan-2026-07-21.md#tl07-lean-execution-evidence-slices)

## 1. Decision boundary

TL0.7.2 proves that one Linux process attempt can be launched and reaped under
the already frozen TL0.7.1 evidence vocabulary. It is a forced synthetic
process-control milestone. It does **not** execute Lean, CTest, `lean4export`,
Axeyum, or any U2 case; it does not write case or completion records; and it
cannot create an official outcome, Axeyum outcome, paired cell, performance
row, population denominator, or parity credit.

The implementation must keep four boundaries explicit:

1. the immutable run and attempt-prelaunch records exist before process
   creation;
2. raw stdout and stderr are files, not in-memory summaries;
3. the terminal record describes only evidence actually observed by the
   adapter; and
4. full immutable checkpoint/resume/completion semantics remain TL0.7.3.

The process adapter may prove `exited`, `signaled`, `wall-timeout`,
`memory-limit`, `launch-failed`, and `preflight-invalid` on the controls below.
The other six TL0.7.1 termination classes remain representable but unobserved.

## 2. Frozen predecessor and research inputs

These are historical inputs to this plan. Later source edits must not silently
change the meaning of this preregistration.

| Input | SHA-256 | Role |
|---|---|---|
| `lean-execution-evidence-v1.json` | `83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a` | exact TL0.7.1 lanes, records, taxonomies, and zero-credit boundary |
| `scripts/gen-lean-execution-evidence.py` | `025f935111b83e1a3bbc78af50a4ad5671baa370bda02fe94756481e54f55418` | validator and canonical JSON/digest semantics |
| `scripts/tests/test_lean_execution_evidence.py` | `1221e20ff4d712233613b03f5cbb75ec943e2b101ff7a370ad511011dc6b13f4` | predecessor mutation gate |
| TL0.7 plan | `0f38bb7944de77a0df28d122c9c1190af3865c8ecc9778cc243135df191f0c37` | process slice and stop conditions |
| Lean implementation plan | `e8a4f6cbc7372a9524f97361f3a30cd6adc1750aaacfe221079d9b07c6867a24` | TL0.7.2 exit wording before this preregistration |
| SMT-COMP local runner | `11a7234b0e7500140d1b7f863860d78bb83287f99d43eb4428ea7546a3c6dbc4` | repository precedent for process groups and sampled Linux `VmHWM` |
| SMT-COMP cgroup enforcement | `47eae7328a58c192e7ed8df0a9bdc426e6ddc505878acff5fe1966c8bc6a462e` | separate aggregate-controller precedent, not reused as TL0.7.2 evidence |
| multi-agent operations guide | `0bc65dc2ab99dd6474ede3be6eb49d302990218a36e902a48dc0aac67fa35e35` | isolated worktree and bounded resource discipline |

The implementation baseline is topic revision
`05146d4f6f6265fd4ff1bd1fde63fab554aa4079`. The preregistration commit will
replace this prose reference in the result with the exact published plan
revision; no probe may run before that revision is pushed.

The design also follows these primary references, observed on 2026-07-22:

- [Python `subprocess`](https://docs.python.org/3/library/subprocess.html):
  argument arrays, exact replacement environments, sessions, timeout cleanup,
  binary output, and mandatory reap after timeout;
- [Python `resource`](https://docs.python.org/3/library/resource.html):
  Unix `RLIMIT_AS`, `RLIMIT_CPU`, and `RUSAGE_CHILDREN` semantics;
- [Linux `/proc` documentation](https://www.kernel.org/doc/html/latest/filesystems/proc.html):
  `VmHWM` is a process peak-resident high-water mark and `VmRSS` is a current
  resident snapshot; and
- [`killpg(3)`](https://man7.org/linux/man-pages/man2/killpg.2.html): a signal
  targets a process group, which is the cleanup unit used below.

These live references explain mechanisms; they are not pinned Lean outcomes or
provider guarantees.

## 3. Planned artifacts and schemas

The implementation may add only the following owned surfaces in this slice:

- `scripts/lean_execution_process.py` — validator and one-attempt adapter;
- `scripts/lean_execution_probe.py` — exact synthetic probe fixture;
- `scripts/fixtures/lean-execution-invalid-interpreter` — executable file whose
  committed bytes pass preflight but whose missing interpreter forces
  `Popen`/`execve` launch failure;
- `scripts/tests/test_lean_execution_process.py` — contract, mutation, and
  live-control tests;
- `docs/plan/evidence/lean-execution-process-tl0.7.2/` — small retained
  canonical records and raw outputs from only the preregistered controls;
- `docs/plan/lean-execution-process-v1.json` — result authority over retained
  control artifacts, with all real/credit counters zero;
- `docs/plan/generated/lean-execution-process.{json,md}` — generated review
  summaries; and
- `docs/plan/lean-execution-process-tl0.7.2-2026-07-22.md` — bounded result.

The adapter accepts canonical JSON with schema
`axeyum-lean-process-spec-v1`. Its exact fields are:

```text
schema, control_id, run_id, attempt_id, sequence, lane_id,
system_profile, credit_class, command, working_directory, environment,
source_files, configuration_sha256, selection_set_id, assigned_case_ids,
wall_timeout_ms, terminate_grace_ms, cooperative_memory_evidence,
expected_terminal_class, spec_sha256
```

The spec is valid only when:

- `system_profile == "synthetic-process-control"`;
- `credit_class == "synthetic-no-credit"`;
- `assigned_case_ids == []` and the selection is the registered synthetic
  empty selection;
- the lane is exactly `standard-local-4g` or `official-export-8g` and the
  inherited `RLIMIT_AS` value is exactly 4,294,967,296 or 8,589,934,592 bytes;
- command is a nonempty array of nonempty strings with an absolute executable
  path and no shell;
- environment is a complete, explicitly supplied string-to-string mapping;
- every source file is a repository-relative regular file with its exact hash;
- timeouts are positive integral milliseconds and the wall timeout exceeds the
  termination grace;
- IDs are safe, unique within the retained result, and sequence is one; and
- `spec_sha256` is the domain-separated digest of every other field.

The output directory must not already exist. One invocation owns exactly one
new directory and may install, in this order:

```text
run.json
stdout.bin
stderr.bin
attempt-prelaunch.json
attempt-terminal.json
```

`run.json` implements the TL0.7.1 run fields. `attempt-prelaunch.json`
implements the immutable attempt fields with `terminal: null`; it is installed
and fsynced before `Popen`. `attempt-terminal.json` implements the separate
attempt-terminal record and references the raw output hashes and the immutable
prelaunch record. TL0.7.2 writes no `case.json`, `completion.json`, JUnit,
provider artifact, or credit record.

Every JSON record is canonical, exact-field, domain-separated, and self-hashed.
Raw bytes are never normalized or decoded to establish identity. A terminal
record contains their byte lengths and SHA-256 hashes. The adapter fails if its
output directory or any target already exists; it never overwrites or treats a
different record as a retry. TL0.7.3 still owns conflict quarantine, kill-point
recovery, directory-specific durable-store qualification, and completion-last
publication.

## 4. Launch and cleanup semantics

The first implementation is Linux/Unix-specific and fail-closed elsewhere.
It performs these steps:

1. validate canonical spec bytes, exact hashes, source files, lane, timeout,
   environment, working directory state, and platform prerequisites;
2. capture the actual local platform without treating a runner label as
   hardware evidence;
3. hash the executable and construct the complete TL0.7.1 run record;
4. create the raw output files and persist the sealed prelaunch attempt;
5. launch with `shell=False`, the exact argument array/environment/directory,
   a new session/process group, and a child-only `RLIMIT_AS` hook;
6. poll with a monotonic clock while sampling the root process's Linux
   `/proc/<pid>/status` `VmHWM`/`VmRSS` fields;
7. on wall timeout, send `SIGTERM` to the process group, wait the exact grace,
   send `SIGKILL` to remaining live group members, and reap the direct child;
8. flush/fsync and hash raw outputs; then
9. install the terminal record.

The adapter must not use `subprocess.run(..., timeout=...)` as proof of whole-
tree cleanup: Python documents that timeout handling applies to the child, not
an independently verified process-group closure. The timeout control therefore
creates a descendant and separately checks that no non-zombie process remains
in the recorded process group.

`peak_rss` is `observed` only when at least one valid root-process sample was
read; it is explicitly root-process scope, not aggregate-tree memory. CPU time
remains `not-observed` in TL0.7.2 because `RUSAGE_CHILDREN` is cumulative and a
generic in-process delta is not an isolated per-attempt controller. Wall time
is observed with a monotonic clock. Swap, PIDs, disk, open files, aggregate
memory, and aggregate CPU remain `not-enforced` or `not-observed` as stated by
the inherited lane; none is inferred from process behavior.

## 5. Terminal classification rules

Classification order is exact and first-match:

1. invalid canonical spec, missing/invalid working directory, unsupported
   platform, or unavailable required limit mechanism -> `preflight-invalid`;
2. `Popen`/`execve` failure after valid preflight -> `launch-failed`;
3. wall watchdog fired -> `wall-timeout`, regardless of the cleanup signal;
4. exact cooperative memory evidence matched -> `memory-limit`;
5. negative return code -> `signaled` with the positive signal number; or
6. nonnegative return code -> `exited`, retaining zero or nonzero exit code.

`memory-limit` is intentionally narrow. All of these must agree:

- lane `RLIMIT_AS` was successfully installed at the exact registered value;
- command executable and probe source hashes equal the committed control;
- the control mode is the registered no-touch anonymous-`mmap`-past-limit
  probe;
- the retained exit code equals the registered nonzero code;
- the exact domain-separated marker is present once in retained stderr; and
- the requested mapping is strictly larger than the effective address-space
  limit and the probe observed `ENOMEM`/`MemoryError`.

The control requests virtual address space but does not touch the mapping, so a
4/8 GiB limit can be tested without consuming 4/8 GiB of physical memory. If
the mapping succeeds, the marker/exit contract fails and the result is merely
`exited`; it is never rewritten as memory exhaustion.

A signal, exit 137, `MemoryError` text, arbitrary child marker, or nonzero exit
alone is not memory evidence. Likewise, the watchdog event, not `SIGKILL`, is
what proves `wall-timeout`. The terminal retains both classification and raw
return/signal facts.

## 6. Frozen control matrix

No other process may enter the retained TL0.7.2 result.

| Ordered ID | Lane | Probe | Required terminal | Required evidence |
|---|---|---|---|---|
| `exit-zero-4g` | `standard-local-4g` | exact probe exits 0 after fixed stdout/stderr | `exited` / code 0 | raw bytes and exit status |
| `exit-seven-4g` | `standard-local-4g` | exact probe exits 7 | `exited` / code 7 | nonzero exit retained without relabeling |
| `self-sigterm-4g` | `standard-local-4g` | exact probe signals itself with `SIGTERM` | `signaled` / signal 15 | negative wait status |
| `wall-timeout-tree-4g` | `standard-local-4g` | exact probe creates one lingering descendant | `wall-timeout` | watchdog event, TERM/KILL sequence as needed, reap, no live group member |
| `memory-limit-4g` | `standard-local-4g` | anonymous `mmap` larger than 4 GiB | `memory-limit` | exact cooperative evidence tuple |
| `memory-limit-8g` | `official-export-8g` | anonymous `mmap` larger than 8 GiB | `memory-limit` | exact cooperative evidence tuple; still adapter-only |
| `invalid-interpreter-4g` | `standard-local-4g` | exact executable fixture has a missing interpreter | `launch-failed` | valid preflight followed by captured launch error |
| `missing-cwd-4g` | `standard-local-4g` | exact probe with a nonexistent working directory | `preflight-invalid` | no process ID and typed preflight diagnostic |

All controls use one worker, one direct launch, no selected case, no network,
no cache, and small raw outputs. Exit/signal/timeout controls use a 2,000 ms
wall limit and 250 ms termination grace; the timeout-tree probe must outlive
that wall limit. Memory controls use a 5,000 ms wall limit and the same grace.
Launch/preflight controls create no child. Exact command/source/marker bytes
will be frozen by the implementation commit before the first retained run.

## 7. Required mutations and assertions

Focused tests must reject or distinguish at least:

1. noncanonical spec JSON or a bad spec self-hash;
2. unknown/changed lane, 4/8 GiB cap, profile, or credit class;
3. relative/empty command, shell string, changed working directory, inherited
   environment, or changed source/executable/configuration identity;
4. pre-existing output directory or output target;
5. launch before the prelaunch record is visibly sealed;
6. `RLIMIT_AS` setup failure or reported effective limit drift;
7. exit 0 versus exit 7 without loss of the nonzero code;
8. signal versus watchdog timeout, including a timeout cleanup signal that
   must not become the primary class;
9. descendant survival after timeout;
10. arbitrary marker, wrong probe/source hash, wrong exit, duplicate marker,
    too-small mapping, or plain signal presented as `memory-limit`;
11. missing/unobserved `/proc` sample represented as numeric zero;
12. raw stdout/stderr hash or byte-size mutation;
13. terminal record created for a different run, attempt, sequence, command,
    or prelaunch record;
14. any case/completion/JUnit/provider artifact created by this slice;
15. any real execution, official/Axeyum outcome, paired cell, performance row,
    denominator, or parity credit; and
16. nondeterministic structural output after removing explicitly observational
    fields such as timestamps, PIDs, wall time, RSS, and platform values.

The live-control test may skip only on a non-Linux platform or when the host
cannot lower `RLIMIT_AS`; the committed retained result may not use a skipped
control. Test timeouts are wider than adapter timeouts and every failure path
must attempt process-group cleanup before returning.

## 8. Acceptance and stop conditions

TL0.7.2 is complete only when:

- this plan was committed and pushed before implementation and any probe;
- the adapter/probe/result source identities are exact and generated review
  artifacts are reproducible;
- all eight ordered controls retain valid prelaunch, raw-output, and terminal
  records with the required classes;
- the timeout descendant is absent or zombie-only after cleanup;
- every mutation above fails closed;
- the base TL0.7.1 and complete-parity gates remain green;
- all real and parity-credit counters remain zero; and
- owned code/docs/link/foundational-resource gates pass, apart from any exact
  unrelated baseline failure recorded separately.

Stop with TL0.7.2 partial if a limit cannot be installed exactly, a process
tree cannot be cleaned and reaped, `/proc` absence becomes a numeric metric,
memory or timeout classification needs inference, retained controls drift from
this matrix, or the implementation would need Lean/CTest/exporter/Axeyum
execution. Do not compensate with a broader claim.

After this slice, TL0.7 remains `PARTIAL`. TL0.7.3 must qualify the immutable
store through forced kill/resume boundaries, and TL0.7.4 must carry two
no-credit real controls through that store before TL0.6.3 can begin.
