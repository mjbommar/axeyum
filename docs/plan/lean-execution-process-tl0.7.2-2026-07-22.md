# TL0.7.2 result — bounded Lean execution process adapter

Status: **complete for synthetic process behavior; no Lean, U2, completion, or parity outcome**

Date: 2026-07-22

Parent:

- [source-first TL0.7.2 plan](lean-execution-process-adapter-tl0.7.2-plan-2026-07-22.md)
- [TL0.7 execution-evidence plan](lean-execution-evidence-tl0.7-plan-2026-07-22.md)
- [TL0.7.1 machine-contract result](lean-execution-evidence-tl0.7.1-2026-07-22.md)
- [complete Lean 4.30 parity contract](lean4-complete-parity-contract-2026-07-22.md)

Machine-readable evidence:

- [result authority](lean-execution-process-v1.json)
- generated [Markdown](generated/lean-execution-process.md) and
  [JSON](generated/lean-execution-process.json)
- [40 retained files](evidence/lean-execution-process-tl0.7.2/) across eight
  exact attempt directories
- [`scripts/lean_execution_process.py`](../../scripts/lean_execution_process.py)
  and [`scripts/lean_execution_probe.py`](../../scripts/lean_execution_probe.py)
- [`scripts/tests/test_lean_execution_process.py`](../../scripts/tests/test_lean_execution_process.py)

## 1. Verdict

TL0.7.2 proves the bounded process behavior required before a real Lean attempt
can enter the durable store. Eight of eight preregistered synthetic controls
retain an exact run identity, prelaunch attempt, raw stdout/stderr, and typed
terminal record. The accepted result contains:

- eight synthetic process attempts under the explicit 4/8 GiB `RLIMIT_AS`
  lanes;
- 40 retained files totaling 35,463 bytes;
- sixteen content-hashed raw stdout/stderr artifacts;
- two normal/nonzero exits, one signal, one descendant-bearing wall timeout,
  two cooperative memory-limit observations, one launch failure, and one
  preflight failure;
- no live non-zombie process-group member after any launched control;
- eleven focused tests covering the preregistered structure, mutations, and
  live controls; and
- zero case records, completion records, JUnit/provider artifacts, real Lean
  runs, official outcomes, Axeyum outcomes, paired cells, performance rows, or
  parity credit.

TL0.7 remains `PARTIAL`. TL0.7.3 must qualify immutable filesystem checkpoints,
kill/resume, conflicts, and completion-last publication. TL0.7.4 may then run
two explicitly no-credit real controls. TL0.6.3 remains blocked until both
slices close.

## 2. Source-first order

The exact control matrix, classification order, resource policy, record order,
and stop conditions were committed and pushed at
`45bf823a46b973a697c45140372540946edcfb0f` before implementation or any
process probe. Adapter/probe/test implementation followed at `b78f1bd2`; the
fresh-checkout executable modes were corrected and pushed at `86f8faef` before
the first live control.

The first validating pass was diagnostic only. Adding the preregistered
reproducible result-authority renderer changed the adapter configuration hash,
so those uncommitted observations were quarantined rather than relabeled. The
final adapter/result implementation was committed and pushed at
`367b9f3401da68981bcef984cc605f9dc000d346`; all 40 authoritative retained
files were then recreated from those exact bytes. The authority rehashes the
plan, adapter, probe, invalid-interpreter fixture, tests, and every retained
file on each check.

No Lean binary, CTest command, exporter, Axeyum executable, or U2 case ran in
either pass.

## 3. Exact observed controls

The generated table is authoritative for observed wall/RSS values. Its fixed
partition is:

| Class | Count | Evidence boundary |
|---|---:|---|
| `exited` | 2 | exact exit codes 0 and 7; nonzero is retained, not relabeled |
| `signaled` | 1 | direct child wait status records `SIGTERM` 15 |
| `wall-timeout` | 1 | monotonic watchdog fired; group TERM then KILL; direct child reaped; no live member |
| `memory-limit` | 2 | exact 4 GiB and 8 GiB `RLIMIT_AS`, committed probe hash, oversized no-touch `mmap`, exit 86, unique marker |
| `launch-failed` | 1 | executable bytes/mode passed preflight; its deliberately absent interpreter made `execve`/`Popen` fail |
| `preflight-invalid` | 1 | nonexistent working directory rejected without creating a child |

The timeout probe creates one descendant and makes both processes ignore
`SIGTERM`. This requires the adapter to escalate to `SIGKILL`, reap the direct
child, scan the recorded group in `/proc`, and prove the residual live-member
set is empty. The cleanup signal remains a raw fact; the watchdog event is what
establishes `wall-timeout`.

The memory probes request 5 GiB and 9 GiB anonymous virtual mappings under the
4 GiB and 8 GiB address-space ceilings without touching the mapping. A
nonzero exit, signal, generic `MemoryError` text, duplicated marker, changed
probe, mapping at/below the limit, or wrong limit cannot establish
`memory-limit`.

## 4. Conservative measurement boundary

Every launched process has an observed monotonic wall duration. Peak RSS is
`observed` only when the adapter sampled a positive Linux root-process
`VmHWM`/`VmRSS`; it is not aggregate process-tree memory. Launch/preflight
failures correctly retain wall and RSS as `not-observed` with `null`, not zero.

CPU time is `not-observed` for all controls. Python documents
`RUSAGE_CHILDREN` as cumulative over terminated and waited-for children, so
TL0.7.2 does not present a generic in-process before/after delta as an isolated
controller measurement. Swap, PIDs, disk, open files, aggregate memory, and
aggregate CPU remain `not-enforced` or `not-observed` exactly as declared.

Mechanism references remain the primary documentation reviewed in the plan:
[Python subprocess](https://docs.python.org/3/library/subprocess.html),
[Python resource limits](https://docs.python.org/3/library/resource.html),
[Linux `/proc`](https://www.kernel.org/doc/html/latest/filesystems/proc.html),
and [`killpg(3)`](https://man7.org/linux/man-pages/man2/killpg.2.html).

## 5. Record and credit boundary

Each attempt directory has exactly five entries:

```text
run.json
stdout.bin
stderr.bin
attempt-prelaunch.json
attempt-terminal.json
```

The prelaunch record is canonical, sealed, and visible before `Popen`. The
terminal record references that exact hash, the raw byte hashes/sizes, exact
run/attempt/sequence, typed metrics, effective `RLIMIT_AS`, process/group IDs,
cleanup events, and diagnostic identity. The validator rejects an extra file,
so a case, completion, JUnit, or provider artifact cannot silently enter this
slice.

The result authority intentionally distinguishes eight **retained synthetic
process attempts** from `real_runs=0`. Neither these attempts nor their timing
and RSS observations enter U2, an official/Axeyum denominator, a performance
comparison, or the A0-A11/G1-G10 terminal conjunction.

## 6. Validation

Reproduction and offline validation:

```sh
python3 -m unittest scripts.tests.test_lean_execution_process
python3 scripts/lean_execution_process.py result --check
python3 -m unittest scripts.tests.test_lean_execution_evidence
python3 scripts/gen-lean-execution-evidence.py --check
python3 -m unittest scripts.tests.test_lean_complete_parity
python3 scripts/gen-lean-complete-parity.py --check
```

The focused suite runs eleven tests. It covers canonical/spec/source/credit
drift; both exact memory evidence tuples; prelaunch-before-spawn order; all
eight controls; descendant liveness; raw/extra/existing-output conflicts;
typed missing metrics; structural determinism after removing observational
fields; exact population closure; and zero-credit generation.

The complete-parity report remains unchanged at 0/10 complete populations,
0/12 complete axes, zero paired cells, 0/10 satisfied terminal gates, and a
disabled terminal claim. The repository-wide link check still has the exact
unrelated baseline failure in the SMT-COMP workstream README for the missing
`checked-finite-profile-quantified-uf-models-2026-07-22.md`; no TL0.7.2 link is
broken.

## 7. Handoff

TL0.7.3 must start with another source-first plan. It may reuse the exact
attempt directory as an input fixture, but it must not rewrite these records or
claim that `O_EXCL` plus fsync in one uninterrupted process already proves the
registered storage class. Its exit requires forced termination at every
persistence boundary, conflict quarantine, repeat/resume equivalence, and a
completion record installed last over all attempts and cases.
