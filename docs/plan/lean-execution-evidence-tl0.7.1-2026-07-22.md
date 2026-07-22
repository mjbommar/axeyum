# TL0.7.1 result — Lean execution-evidence contract

Status: **complete as a machine contract; no process or parity outcome**

Date: 2026-07-22

Parent:

- [preregistered TL0.7 plan](lean-execution-evidence-tl0.7-plan-2026-07-22.md)
- [complete Lean 4.30 parity contract](lean4-complete-parity-contract-2026-07-22.md)
- [TL0.6.2 official CI profiles](lean-u2-official-ci-profiles-tl0.6.2-2026-07-22.md)

Machine-readable evidence:

- [execution-evidence authority](lean-execution-evidence-v1.json)
- generated [Markdown](generated/lean-execution-evidence.md) and
  [JSON](generated/lean-execution-evidence.json) summaries
- [`scripts/gen-lean-execution-evidence.py`](../../scripts/gen-lean-execution-evidence.py)
- [`scripts/tests/test_lean_execution_evidence.py`](../../scripts/tests/test_lean_execution_evidence.py)

## 1. Verdict

TL0.7.1 closes the representation question that precedes any retained Lean
execution: Axeyum can now state exactly what a lane policy, pre-launch run
identity, process attempt, case record, artifact, completion, and zero-credit
partial bundle must contain. It does not launch or observe a process.

The exact bounded result is:

- two local lane templates: explicit 4 GiB standard and 8 GiB official-export;
- twelve typed termination classes;
- seven exact record contracts covering run, attempt, attempt terminal, case,
  artifact, completion, and credits;
- five validating synthetic lifecycle controls;
- nineteen fail-closed mutation classes covered by twelve unit tests; and
- zero real runs, executed attempts, completed cases, official outcomes,
  Axeyum outcomes, paired cells, or performance rows.

TL0.7 remains `PARTIAL`: process behavior, durable filesystem installation,
and no-credit real controls belong to TL0.7.2--TL0.7.4. TL0.6.3 therefore
remains blocked.

## 2. Source-first order

The complete schema, lane policies, termination taxonomy, checkpoint rules,
credit predicates, mutation register, and stop conditions were committed and
pushed at `ff8f8dd4` before implementation or synthetic validation. The
authority binds that commit and the preregistered plan hash. Current-file
inputs such as the plan, TL0.6.2 profile authority, `mem-run.sh`, ADR-0344, and
ADR-0345 are rehashed during normal validation; explicitly labeled baseline
inputs remain historical identities rather than silently following later
roadmap edits.

No Lean, CTest, exporter, Axeyum executable, or fixture entered any synthetic
control. The controls use invented case, runner, executable, and artifact
identities and are structurally unable to earn credit.

## 3. Registered lane templates

| Lane | Address-space ceiling | Worker ceiling | Allowed credit |
|---|---:|---:|---|
| `standard-local-4g` | 4,294,967,296 bytes | 2 | local development/contract only |
| `official-export-8g` | 8,589,934,592 bytes | 1 | official adapter/export only |

The contract explicitly distinguishes a configured ceiling from an observed
peak. Both policies instantiate the current per-process `RLIMIT_AS` mechanism;
they do not claim aggregate cgroup enforcement, swap control, or peak RSS
measurement. Those are typed fields whose state may be `observed`,
`not-observed`, or `not-enforced`, never an ambiguous zero.

The existing generic wrapper defaults to 64 GiB. A run must therefore record
an explicit `MEM_LIMIT_GB=4` or `MEM_LIMIT_GB=8`; invoking the wrapper without
that value cannot instantiate either registered lane. A future official CTest
reproduction envelope is a separate content-identified policy, not an alias of
these local templates.

## 4. Records and typed termination

The authority fixes exact field sets for:

- a run identity binding source/selection, executable/configuration, command,
  working directory, environment, resources, actual platform, and artifact
  policy before launch;
- an attempt recorded before process creation, with assignment, raw artifacts,
  terminal or deliberate absence, and self-hash;
- a terminal record retaining exit code, signal, enforcement events, and
  independent typed state/value/unit records for wall time, CPU time, and peak
  RSS;
- per-case records joined to the exact TL0.6 selection and owning attempt;
- provider/local artifacts with content identity, size, expiry state, and
  durable-copy identity;
- completion installed last over exact attempt/case/artifact record-set
  digests; and
- a closed credit object that is all zero for synthetic/incomplete bundles.

The twelve termination classes are `exited`, `signaled`, `wall-timeout`,
`cpu-timeout`, `memory-limit`, `pids-limit`, `disk-limit`, `cancelled`,
`runner-lost`, `launch-failed`, `preflight-invalid`, and
`unknown-termination`. `memory-limit`, timeout, PID, and disk-limit records
require their matching enforcement event. A nonzero exit or signal cannot be
relabeled as OOM.

## 5. Synthetic validation

Five no-process controls exercise the schema:

| Control | Representation proved |
|---|---|
| `clean-complete` | two passed cases plus completion-last closure |
| `failed-case-complete` | a failed case remains visible in a completed run |
| `interrupted-resumed` | a terminal-less attempt remains accounted beside its retry |
| `incomplete` | partial diagnostic data has no completion or credit |
| `preflight-invalid` | rejected preflight has an attempt but no launched cases or credit |

The twelve unit tests cover all nineteen preregistered mutation families:
source/lane drift, implicit wrapper defaults, malformed resources, runner
substitution, run identity, attempt closure, guessed termination, case closure
and attribution, artifact identity/retention/conflicts, sidecar-only and early
completion, lost attempts, incomplete credit, profile promotion, and real
outcomes in the contract authority.

Reproduction:

```sh
python3 -m unittest scripts.tests.test_lean_execution_evidence
python3 scripts/gen-lean-execution-evidence.py --check
```

## 6. Corrections and non-claims

This milestone prevents several plausible overclaims:

1. Lean's pinned workflow resolves `NPROC` from the live runner and declares no
   job-wide memory cap. The workflow label is not effective resource evidence.
2. Current GitHub timeout/hardware defaults are provider state, not historical
   properties of the pinned Lean commit. Each run must retain its effective
   configured and observed values.
3. CTest exit, JUnit, logs, provider conclusions, and expiring provider
   artifacts are sidecars. None proves exact case/attempt completion alone.
4. A completed run may retain failed cases. Completion means evidence closure,
   not success.
5. Adapter/export evidence stays separate from native-system parity.

The generated complete-parity report still has zero complete U0--U9
authorities, zero complete A0--A11 axes, zero paired cells, and zero satisfied
G1--G10 gates.

## 7. Handoff

TL0.7.2 must implement the process adapter and use forced controls to retain
exact launch, exit, signal, timeout, cooperative memory-limit, and preflight
failures without guessed classification or orphaned descendants. TL0.7.3 then
owns actual same-directory atomic checkpoints, conflict quarantine, kill at
each persistence boundary, resume, and completion-last equivalence on every
claimed storage class. TL0.7.4 may run only two no-credit real controls.

Only after those slices close may TL0.6.3 start retaining the 111 official
CTest profile attempts. Their actual runner/platform envelopes must be
registered separately; neither local lane template is automatically an
official-platform reproduction.
